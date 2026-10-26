import GHS.TauCompact

/-!
# Continuity and uniqueness of the compactified welfare extension

This file verifies the global continuity and unique-extension claims for the
extended welfare used in Appendix B. The compactified coordinate
`τ : ι → ℝ≥0∞` represents `p = α - τ`, including `p_i = -∞` when
`τ_i = ∞`.
-/

open Set Filter Topology

namespace GHS
namespace WelfareDual

variable {ι : Type*} [Fintype ι] (W : WelfareDual ι)

set_option maxHeartbeats 800000

/-- The loss whose negative is the extended affine payoff. -/
noncomputable def extLoss (α μ : ι → ℝ) (τ : ι → ENNReal) : EReal :=
  ((W.cost μ - μ ⬝ᵥ α : ℝ) : EReal) + (tauPair μ τ : EReal)

theorem extPayoff_eq_neg_extLoss (α μ : ι → ℝ) (τ : ι → ENNReal) :
    W.extPayoff α μ τ = -W.extLoss α μ τ := by
  unfold extPayoff extLoss
  by_cases htop : tauPair μ τ = ⊤
  · have htopE : ((tauPair μ τ : ENNReal) : EReal) = ⊤ := by
      rw [htop]
      rfl
    rw [htopE, EReal.sub_top, EReal.add_top_of_ne_bot,
      EReal.neg_top]
    exact EReal.coe_ne_bot _
  · rw [← EReal.coe_ennreal_toReal htop, ← EReal.coe_sub,
      ← EReal.coe_add, ← EReal.coe_neg]
    congr 1
    ring

/-- The loss is jointly lower semicontinuous in a feasible dual vector and a
compactified waiting-time vector. -/
theorem lowerSemicontinuous_extLoss (α : ι → ℝ) :
    LowerSemicontinuous fun z : W.D × (ι → ENNReal) =>
      W.extLoss α z.1 z.2 := by
  have hcost : LowerSemicontinuous fun μ : W.D => W.cost μ :=
    lowerSemicontinuous_restrict_iff.mpr W.hcost_lsc
  have hdot : Continuous fun μ : W.D => μ.1 ⬝ᵥ α := by
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const
  have hbaseReal : LowerSemicontinuous fun z : W.D × (ι → ENNReal) =>
      W.cost z.1 - z.1.1 ⬝ᵥ α := by
    have hnegdot : Continuous fun z : W.D × (ι → ENNReal) =>
        -(z.1.1 ⬝ᵥ α) := continuous_neg.comp (hdot.comp continuous_fst)
    simpa only [sub_eq_add_neg] using
      (hcost.comp continuous_fst).add hnegdot.lowerSemicontinuous
  have hbase : LowerSemicontinuous fun z : W.D × (ι → ENNReal) =>
      ((W.cost z.1 - z.1.1 ⬝ᵥ α : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp_lowerSemicontinuous hbaseReal
      fun _ _ h => EReal.coe_le_coe_iff.mpr h
  have hmap : Continuous fun z : W.D × (ι → ENNReal) =>
      (z.1.1, z.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hpairENN : LowerSemicontinuous fun z : W.D × (ι → ENNReal) =>
      tauPair z.1.1 z.2 :=
    lowerSemicontinuous_tauPair_joint.comp hmap
  have hpair : LowerSemicontinuous fun z : W.D × (ι → ENNReal) =>
      (tauPair z.1.1 z.2 : EReal) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hpairENN
      fun _ _ h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  unfold extLoss
  refine hbase.add' hpair fun z => ?_
  exact EReal.continuousAt_add
    (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))

/-- The extended affine payoff is jointly upper semicontinuous in the dual
vector and compactified waiting time. -/
theorem upperSemicontinuous_extPayoff_joint (α : ι → ℝ) :
    UpperSemicontinuous fun z : W.D × (ι → ENNReal) =>
      W.extPayoff α z.1 z.2 := by
  have h := continuous_neg.comp_lowerSemicontinuous_antitone
    (W.lowerSemicontinuous_extLoss α) fun _ _ h => EReal.neg_le_neg_iff.2 h
  simpa only [Function.comp_apply, W.extPayoff_eq_neg_extLoss] using h

/-- At every compactified waiting-time vector, some feasible dual vector
attains the supremum defining the extended welfare. -/
theorem exists_extPayoff_eq_Gext (α : ι → ℝ) (τ : ι → ENNReal) :
    ∃ μ : W.D, W.Gext α τ = W.extPayoff α μ τ := by
  letI : Nonempty W.D := ⟨⟨0, W.hD_zero⟩⟩
  letI : CompactSpace W.D := isCompact_iff_compactSpace.mp W.hD_compact
  have husc : UpperSemicontinuous fun μ : W.D => W.extPayoff α μ τ := by
    have hpair : Continuous fun μ : W.D => (μ, τ) :=
      continuous_id.prodMk continuous_const
    change UpperSemicontinuous
      ((fun z : W.D × (ι → ENNReal) => W.extPayoff α z.1 z.2) ∘
        fun μ : W.D => (μ, τ))
    exact (W.upperSemicontinuous_extPayoff_joint α).comp hpair
  obtain ⟨μ, -, hmax⟩ := (husc.upperSemicontinuousOn Set.univ).exists_isMaxOn
    (univ_nonempty : (Set.univ : Set W.D).Nonempty) isCompact_univ
  refine ⟨μ, le_antisymm ?_ ?_⟩
  · exact iSup_le fun ν => hmax (mem_univ ν)
  · exact le_iSup (fun ν : W.D => W.extPayoff α ν τ) μ

/-- The compactified welfare is upper semicontinuous. The proof uses the
attained maximum and projects a compact upper-level set. -/
theorem upperSemicontinuous_Gext (α : ι → ℝ) :
    UpperSemicontinuous (W.Gext α) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  letI : CompactSpace W.D := isCompact_iff_compactSpace.mp W.hD_compact
  let S : Set (W.D × (ι → ENNReal)) :=
    {z | c ≤ W.extPayoff α z.1 z.2}
  have hSclosed : IsClosed S := by
    exact (W.upperSemicontinuous_extPayoff_joint α).isClosed_preimage c
  have hScpt : IsCompact S := hSclosed.isCompact
  have heq : W.Gext α ⁻¹' Ici c = Prod.snd '' S := by
    ext τ
    constructor
    · intro hτ
      change c ≤ W.Gext α τ at hτ
      obtain ⟨μ, hμ⟩ := W.exists_extPayoff_eq_Gext α τ
      refine ⟨(μ, τ), ?_, rfl⟩
      change c ≤ W.extPayoff α μ τ
      rwa [← hμ]
    · rintro ⟨z, hz, rfl⟩
      change c ≤ W.Gext α z.2
      exact hz.trans (le_iSup (fun μ : W.D => W.extPayoff α μ z.2) z.1)
  rw [heq]
  exact (hScpt.image continuous_snd).isClosed

/-- The extended welfare is continuous on the full compactified domain. -/
theorem continuous_Gext (α : ι → ℝ) : Continuous (W.Gext α) :=
  continuous_iff_lower_upperSemicontinuous.mpr
    ⟨W.lowerSemicontinuous_Gext α, W.upperSemicontinuous_Gext α⟩

/-- Finite truncation of compactified waiting times. -/
noncomputable def tauTrunc (τ : ι → ENNReal) (n : ℕ) : ι → ENNReal :=
  fun i => τ i ⊓ (n : ENNReal)

/-- The real vector underlying a finite truncation. -/
noncomputable def tauTruncReal (τ : ι → ENNReal) (n : ℕ) : ι → ℝ :=
  fun i => (tauTrunc τ n i).toReal

theorem tauTruncReal_nonneg (τ : ι → ENNReal) (n : ℕ) :
    0 ≤ tauTruncReal τ n := by
  intro i
  exact ENNReal.toReal_nonneg

theorem tauOfReal_tauTruncReal (τ : ι → ENNReal) (n : ℕ) :
    tauOfReal (tauTruncReal τ n) = tauTrunc τ n := by
  funext i
  unfold tauOfReal tauTruncReal tauTrunc
  rw [ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top inf_le_right

theorem tendsto_tauTrunc (τ : ι → ENNReal) :
    Tendsto (tauTrunc τ) atTop (𝓝 τ) := by
  rw [tendsto_pi_nhds]
  intro i
  have hconst : Tendsto (fun _ : ℕ => τ i) atTop (𝓝 (τ i)) := tendsto_const_nhds
  have h := hconst.inf_nhds ENNReal.tendsto_nat_nhds_top
  simpa [tauTrunc] using h

/-- Any continuous function agreeing with the finite welfare at every finite
nonnegative waiting time agrees with the compactified extension everywhere. -/
theorem eq_Gext_of_continuous_of_eq_finite
    (hDpos : ∀ μ ∈ W.D, 0 ≤ μ) (α : ι → ℝ)
    (F : (ι → ENNReal) → EReal) (hF : Continuous F)
    (hfinite : ∀ t : ι → ℝ, 0 ≤ t →
      F (tauOfReal t) = ((W.Gfn (α - t) : ℝ) : EReal)) :
    F = W.Gext α := by
  funext τ
  have ht := tendsto_tauTrunc τ
  have hFt : Tendsto (fun n => F (tauTrunc τ n)) atTop (𝓝 (F τ)) :=
    hF.continuousAt.tendsto.comp ht
  have hGt : Tendsto (fun n => W.Gext α (tauTrunc τ n))
      atTop (𝓝 (W.Gext α τ)) :=
    (W.continuous_Gext α).continuousAt.tendsto.comp ht
  have heq : (fun n => F (tauTrunc τ n)) =
      fun n => W.Gext α (tauTrunc τ n) := by
    funext n
    rw [← tauOfReal_tauTruncReal τ n,
      hfinite (tauTruncReal τ n) (tauTruncReal_nonneg τ n),
      W.Gext_tauOfReal hDpos α (tauTruncReal_nonneg τ n)]
  rw [heq] at hFt
  exact tendsto_nhds_unique hFt hGt

end WelfareDual
end GHS
