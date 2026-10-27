import GHS.TauCompact

/-!
# Universal limit form of Theorem 3.1

The existence theorems in `TauCompact` construct one deferred-acceptance run.
This file records the stronger form used in the paper: the limit conclusions
hold for every run satisfying the algorithm's step certificates and every
convergent proposal subsequence.
-/

namespace GHS

open Filter Topology

variable {ι : Type*} [Fintype ι] {WG WH : WelfareDual ι} {α γ : ι → ℝ}

/-- For any certified run and any convergent proposal subsequence, tentative
acceptances have the same limit, and the raw least waiting-time sequences
converge to exact Kuhn--Tucker multipliers at that limit. -/
theorem theorem3_exact_limits_of_run
    (hcG : Exchangeable WG.cFn) (hcH : Exchangeable WH.cFn)
    (hDGpos : ∀ q ∈ WG.D, 0 ≤ q) (hDHpos : ∀ q ∈ WH.D, 0 ≤ q)
    (hDGconv : Convex ℝ WG.D) (hDHconv : Convex ℝ WH.D)
    (hGcost_conv : ConvexOn ℝ WG.D WG.cost)
    (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    (s : DASequences ι)
    (hrejG : ∀ k, s.A k - s.P k ∈ WG.rejectSet α (s.A k))
    (hrejH : ∀ k, s.P k - s.T k ∈ WH.rejectSet γ (s.P k))
    (hcross : ∀ k, s.T k ≤ s.P (k + 1))
    {μ : ι → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hPt : Tendsto (fun k => s.P (φ k)) atTop (𝓝 μ)) :
    ∃ rawP rawT : ι → ENNReal,
      Tendsto (fun k => s.T (φ k)) atTop (𝓝 μ) ∧
      0 ≤ μ ∧ μ ≤ s.Ainf ∧
      s.Ainf - μ ∈ WG.rejectSet α s.Ainf ∧
      0 ∈ WH.rejectSet γ μ ∧
      rawP = DASequences.proposerTauLimit WG s α ∧
      rawT = DASequences.receiverTauLimit WH s γ ∧
      Tendsto (DASequences.proposerTau WG s α) atTop (𝓝 rawP) ∧
      Tendsto (DASequences.receiverTau WH s γ) atTop (𝓝 rawT) ∧
      rawP ∈ WG.tauMinSet α s.Ainf ∧ rawT ∈ WH.tauMinSet γ μ ∧
      WG.ExtTight α μ rawP ∧ WelfareDual.TauSlack s.Ainf μ rawP ∧
      WH.ExtTight γ μ rawT ∧ WelfareDual.TauSlack μ μ rawT := by
  have hTt : Tendsto (fun k => s.T (φ k)) atTop (𝓝 μ) :=
    s.tendsto_T_subseq_of_tendsto_P hφ hPt
  have hμ0 : 0 ≤ μ := by
    intro i
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds
      (tendsto_pi_nhds.mp hPt i) fun k => ?_
    exact le_trans (s.nonneg_T (φ k) i) (s.T_le_P (φ k) i)
  have hAt : Tendsto (fun k => s.A (φ k)) atTop (𝓝 s.Ainf) :=
    s.tendsto_A.comp hφ.tendsto_atTop
  have hμA : μ ≤ s.Ainf := by
    intro i
    refine le_of_tendsto_of_tendsto' (tendsto_pi_nhds.mp hPt i)
      (tendsto_pi_nhds.mp hAt i) fun k => s.P_le_A (φ k) i
  have hG : s.Ainf - μ ∈ WG.rejectSet α s.Ainf := by
    refine WG.rejectSet_limit_antitone α s.nonneg_Ainf
      (fun k => s.Ainf_le (φ k)) hAt (hAt.sub hPt) ?_
    exact fun k => hrejG (φ k)
  have hH : 0 ∈ WH.rejectSet γ μ := by
    refine WH.rejectSet_fixedPoint_of_tendsto hDHconv hHcost_conv hDHpos γ
      (fun k => (s.nonneg_T (φ k)).trans (s.T_le_P (φ k)))
      (fun k => hrejH (φ k)) hPt hTt
  have hmono := DASequences.monotone_proposerTau WG s hcG hDGpos
    hDGconv hGcost_conv α
  have hanti := DASequences.antitone_receiverTau WH s hcH hDHpos
    hDHconv hHcost_conv γ hcross hrejH
  let rawP := DASequences.proposerTauLimit WG s α
  let rawT := DASequences.receiverTauLimit WH s γ
  have hrawPt : Tendsto (DASequences.proposerTau WG s α) atTop (𝓝 rawP) :=
    DASequences.tendsto_proposerTau WG s α hmono
  have hrawTt : Tendsto (DASequences.receiverTau WH s γ) atTop (𝓝 rawT) :=
    DASequences.tendsto_receiverTau WH s γ hanti
  have hrawPmem : rawP ∈ WG.tauMinSet α s.Ainf := by
    apply WG.tauMinSet_limit hDGpos hDGconv hGcost_conv α
      (fun k => s.nonneg_A k) s.nonneg_Ainf s.tendsto_A hrawPt
    intro k
    exact WG.tauInf_mem hcG hDGpos hDGconv hGcost_conv α (s.A k)
      (s.nonneg_A k)
  have hrawTmem : rawT ∈ WH.tauMinSet γ μ := by
    apply WH.tauMinSet_limit hDHpos hDHconv hHcost_conv γ
      (fun k => (s.nonneg_T (φ k)).trans (s.T_le_P (φ k))) hμ0 hPt
      (hrawTt.comp hφ.tendsto_atTop)
    intro k
    exact WH.tauInf_mem hcH hDHpos hDHconv hHcost_conv γ (s.P (φ k))
      ((s.nonneg_T (φ k)).trans (s.T_le_P (φ k)))
  have hμDG : μ ∈ WG.D := by
    obtain ⟨-, hD, -⟩ :=
      (WG.mem_rejectSet_iff_acceptance s.nonneg_Ainf).mp hG
    rwa [sub_sub_cancel] at hD
  have hoptG : WG.boxValue α s.Ainf = μ ⬝ᵥ α - WG.cost μ := by
    have h := WG.boxValue_eq_of_mem_rejectSet s.nonneg_Ainf hG
    rwa [sub_sub_cancel] at h
  have hkG := (WG.mem_tauMinSet_iff_kkt hDGpos hDGconv hGcost_conv α
    s.nonneg_Ainf hμDG hμA hoptG rawP).mp hrawPmem
  have hμDH : μ ∈ WH.D := by
    obtain ⟨-, hD, -⟩ := (WH.mem_rejectSet_iff_acceptance hμ0).mp hH
    rwa [sub_zero] at hD
  have hoptH : WH.boxValue γ μ = μ ⬝ᵥ γ - WH.cost μ := by
    have h := WH.boxValue_eq_of_mem_rejectSet hμ0 hH
    rwa [sub_zero] at h
  have hkH := (WH.mem_tauMinSet_iff_kkt hDHpos hDHconv hHcost_conv γ
    hμ0 hμDH le_rfl hoptH rawT).mp hrawTmem
  exact ⟨rawP, rawT, hTt, hμ0, hμA, hG, hH, rfl, rfl, hrawPt,
    hrawTt, hrawPmem, hrawTmem, hkG.1, hkG.2, hkH.1, hkH.2⟩

/-- The normalized exact-equilibrium conclusion of Theorem 3.1 holds for
every certified run and every convergent proposal subsequence. -/
theorem theorem3_exact_equilibrium_of_run
    (hcG : Exchangeable WG.cFn) (hcH : Exchangeable WH.cFn)
    (hDGpos : ∀ q ∈ WG.D, 0 ≤ q) (hDHpos : ∀ q ∈ WH.D, 0 ≤ q)
    (hDGconv : Convex ℝ WG.D) (hDHconv : Convex ℝ WH.D)
    (hGcost_conv : ConvexOn ℝ WG.D WG.cost)
    (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    {nG nH : ι → ℝ} (_hnG0 : 0 ≤ nG) (_hnH0 : 0 ≤ nH)
    (hDGbound : ∀ ν ∈ WG.D, ν ≤ nG)
    (hDHbound : ∀ ν ∈ WH.D, ν ≤ nH)
    (s : DASequences ι) (hs0 : s.A 0 = nG ⊓ nH)
    (hrejG : ∀ k, s.A k - s.P k ∈ WG.rejectSet α (s.A k))
    (hrejH : ∀ k, s.P k - s.T k ∈ WH.rejectSet γ (s.P k))
    (hcross : ∀ k, s.T k ≤ s.P (k + 1))
    {μ : ι → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hPt : Tendsto (fun k => s.P (φ k)) atTop (𝓝 μ)) :
    ∃ rawP rawT τα τγ : ι → ENNReal,
      Tendsto (fun k => s.T (φ k)) atTop (𝓝 μ) ∧
      0 ≤ μ ∧ μ ≤ s.Ainf ∧
      s.Ainf - μ ∈ WG.rejectSet α s.Ainf ∧
      0 ∈ WH.rejectSet γ μ ∧
      rawP = DASequences.proposerTauLimit WG s α ∧
      rawT = DASequences.receiverTauLimit WH s γ ∧
      Tendsto (DASequences.proposerTau WG s α) atTop (𝓝 rawP) ∧
      Tendsto (DASequences.receiverTau WH s γ) atTop (𝓝 rawT) ∧
      τα = WelfareDual.normalizeTau nG μ rawP ∧
      τγ = WelfareDual.normalizeTau nH μ rawT ∧
      τα ∈ WG.tauMinSet α s.Ainf ∧ τγ ∈ WH.tauMinSet γ μ ∧
      WG.ExtTight α μ τα ∧ WelfareDual.TauSlack s.Ainf μ τα ∧
      WH.ExtTight γ μ τγ ∧ WelfareDual.TauSlack μ μ τγ ∧
      ∀ i, τα i ⊓ τγ i = 0 := by
  obtain ⟨rawP, rawT, hTt, hμ0, hμA, hG, hH, hrawPdef,
    hrawTdef, hrawPt, hrawTt, hrawPmem, hrawTmem, htightP, hslackP,
    htightT, hslackT⟩ :=
    theorem3_exact_limits_of_run (WG := WG) (WH := WH) (α := α) (γ := γ)
      hcG hcH hDGpos hDHpos hDGconv hDHconv hGcost_conv hHcost_conv
      s hrejG hrejH hcross hφ hPt
  have hμDG : μ ∈ WG.D := by
    obtain ⟨-, hD, -⟩ :=
      (WG.mem_rejectSet_iff_acceptance s.nonneg_Ainf).mp hG
    rwa [sub_sub_cancel] at hD
  have hμDH : μ ∈ WH.D := by
    obtain ⟨-, hD, -⟩ := (WH.mem_rejectSet_iff_acceptance hμ0).mp hH
    rwa [sub_zero] at hD
  let τα := WelfareDual.normalizeTau nG μ rawP
  let τγ := WelfareDual.normalizeTau nH μ rawT
  have htightα : WG.ExtTight α μ τα :=
    WG.extTight_normalize hDGpos hμDG hDGbound htightP
  have hslackα : WelfareDual.TauSlack s.Ainf μ τα :=
    WelfareDual.tauSlack_normalize hμA hslackP
  have htightγ : WH.ExtTight γ μ τγ :=
    WH.extTight_normalize hDHpos hμDH hDHbound htightT
  have hslackγ : WelfareDual.TauSlack μ μ τγ :=
    WelfareDual.tauSlack_normalize le_rfl hslackT
  have hταmem : τα ∈ WG.tauMinSet α s.Ainf :=
    (WG.tauObjective_eq_of_kkt hDGpos α s.nonneg_Ainf hμDG hμA
      htightα hslackα).2
  have hτγmem : τγ ∈ WH.tauMinSet γ μ :=
    (WH.tauObjective_eq_of_kkt hDHpos γ hμ0 hμDH le_rfl
      htightγ hslackγ).2
  have hminzero : ∀ i, τα i ⊓ τγ i = 0 := by
    intro i
    by_cases hα0 : τα i = 0
    · simp [hα0]
    by_cases hγ0 : τγ i = 0
    · simp [hγ0]
    exfalso
    have hμneG : μ i ≠ nG i := by
      intro h
      apply hα0
      simp [τα, WelfareDual.normalizeTau, h]
    have hμneH : μ i ≠ nH i := by
      intro h
      apply hγ0
      simp [τγ, WelfareDual.normalizeTau, h]
    have hrawP0 : rawP i ≠ 0 := by
      intro h
      apply hα0
      simp [τα, WelfareDual.normalizeTau, h]
    have hrawT0 : rawT i ≠ 0 := by
      intro h
      apply hγ0
      simp [τγ, WelfareDual.normalizeTau, h]
    have hμltG : μ i < nG i := lt_of_le_of_ne (hDGbound μ hμDG i) hμneG
    have hμltH : μ i < nH i := lt_of_le_of_ne (hDHbound μ hμDH i) hμneH
    have hseqT0 (k : ℕ) : DASequences.receiverTau WH s γ k i ≠ 0 := by
      intro hk0
      apply hrawT0
      apply le_antisymm
      · rw [hrawTdef]
        exact iInf_le_of_le k (by rw [hk0])
      · exact bot_le
    have hPTeq (k : ℕ) : s.P k i = s.T k i := by
      apply le_antisymm
      · by_contra hne
        have hlt : s.T k i < s.P k i := lt_of_not_ge hne
        have hz := WelfareDual.tau_eq_zero_of_slack_of_lt
          (DASequences.receiverTau_slack WH s hcH hDHpos hDHconv
            hHcost_conv γ hrejH k) hlt
        exact hseqT0 k hz
      · exact s.T_le_P k i
    have hAconst : ∀ k, s.A k i = (nG ⊓ nH) i := by
      intro k
      induction k with
      | zero => exact congrFun hs0 i
      | succ k ih =>
          rw [s.update k]
          change s.A k i - (s.P k i - s.T k i) = (nG ⊓ nH) i
          rw [hPTeq k, sub_self, sub_zero, ih]
    have hAinf : s.Ainf i = (nG ⊓ nH) i := by
      unfold DASequences.Ainf
      simp_rw [hAconst]
      simp
    have hμAeq : μ i = s.Ainf i := by
      apply le_antisymm (hμA i)
      apply le_of_not_gt
      intro hlt
      exact hrawP0 (WelfareDual.tau_eq_zero_of_slack_of_lt hslackP hlt)
    have hμinit : μ i = (nG ⊓ nH) i := hμAeq.trans hAinf
    rcases le_total (nG i) (nH i) with hGH | hHG
    · have hi : (nG ⊓ nH) i = nG i := by
        simp only [Pi.inf_apply, inf_eq_left.mpr hGH]
      rw [hi] at hμinit
      exact hμneG hμinit
    · have hi : (nG ⊓ nH) i = nH i := by
        simp only [Pi.inf_apply, inf_eq_right.mpr hHG]
      rw [hi] at hμinit
      exact hμneH hμinit
  exact ⟨rawP, rawT, τα, τγ, hTt, hμ0, hμA, hG, hH, hrawPdef,
    hrawTdef, hrawPt, hrawTt, rfl, rfl, hταmem, hτγmem, htightα,
    hslackα, htightγ, hslackγ, hminzero⟩

end GHS
