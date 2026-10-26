import GHS.MidpointClosure
import GHS.Conjugacy

/-!
# Extended-valued exchangeability implies convexity

This file proves the full extended-valued form of GHS Proposition A.1.  The
proof is the compact midpoint argument used in the paper, now carried out for
`EReal`-valued functions.  Lower semicontinuity closes the midpoint-stable
epigraph, and `convex_of_isClosed_midpoint_mem` then yields convexity.
-/

open Set

namespace GHS

/-- Midpoint inequality for a lower-semicontinuous exchangeable
extended-valued function at two points of its effective domain. -/
theorem midpoint_le_of_exchangeable_ereal {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hbot : ∀ x, f x ≠ ⊥) (hlsc : LowerSemicontinuous f)
    (hex : QOrderE f f) (q q' : Fin n → ℝ) :
    f ((q + q') / 2) + f ((q + q') / 2) ≤ f q + f q' := by
  classical
  set m : Fin n → ℝ := (q + q') / 2 with hm
  have hmi : ∀ i, m i = (q i + q' i) / 2 := fun i => rfl
  set lo : Fin n → ℝ := q ⊓ q' with hlo
  set hi : Fin n → ℝ := q ⊔ q' with hhi
  set box : Set (Fin n → ℝ) := Icc lo hi with hbox
  set C : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | p.1 ∈ box} ∩ {p | p.2 ∈ box} ∩ {p | p.1 + p.2 = q + q'} ∩
      {p | f p.1 + f p.2 ≤ f q + f q'} with hC
  set g₀ : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun p => l1Dist m p.1 + l1Dist m p.2 with hg₀
  have hg₀cont : Continuous g₀ :=
    ((continuous_l1Dist m).comp continuous_fst).add
      ((continuous_l1Dist m).comp continuous_snd)
  have hboxcompact : IsCompact box := isCompact_Icc
  have hboxclosed : IsClosed box := hboxcompact.isClosed
  have hCclosed : IsClosed C := by
    refine (((hboxclosed.preimage continuous_fst).inter
      (hboxclosed.preimage continuous_snd)).inter
      (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)).inter ?_
    have hlsc1 : LowerSemicontinuous
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1) :=
      hlsc.comp continuous_fst
    have hlsc2 : LowerSemicontinuous
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.2) :=
      hlsc.comp continuous_snd
    have hadd : LowerSemicontinuous
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 + f p.2) :=
      hlsc1.add' hlsc2 fun p =>
        EReal.continuousAt_add (Or.inr (hbot p.2)) (Or.inl (hbot p.1))
    exact lowerSemicontinuous_iff_isClosed_preimage.mp hadd (f q + f q')
  have hCsub : C ⊆ box ×ˢ box := fun p hp => ⟨hp.1.1.1, hp.1.1.2⟩
  have hCcompact : IsCompact C :=
    (hboxcompact.prod hboxcompact).of_isClosed_subset hCclosed hCsub
  have hqmem : (q, q') ∈ C :=
    ⟨⟨⟨⟨inf_le_left, le_sup_left⟩, ⟨inf_le_right, le_sup_right⟩⟩, rfl⟩,
      le_refl (f q + f q')⟩
  obtain ⟨⟨u, u'⟩, humem, humin⟩ :=
    hCcompact.exists_isMinOn ⟨(q, q'), hqmem⟩ hg₀cont.continuousOn
  have key : ∀ v v', (v, v') ∈ C → IsMinOn g₀ C (v, v') → v ≤ m := by
    intro v v' hmem hmin
    obtain ⟨⟨⟨hv_box, hv'_box⟩, hsum⟩, hf_le⟩ := hmem
    set δ₁ : Fin n → ℝ := (2⁻¹ : ℝ) • (v - v')⁺ with hδ₁def
    have hδ₁i : ∀ i, δ₁ i = (v i - v' i)⁺ / 2 := by
      intro i
      simp only [hδ₁def, Pi.smul_apply, smul_eq_mul, posPart_apply, Pi.sub_apply]
      ring
    have hδ₁mem : δ₁ ∈ Icc 0 ((v - v')⁺) := by
      constructor <;> intro i
      · rw [hδ₁i i]
        exact div_nonneg (posPart_nonneg _) (by norm_num)
      · rw [hδ₁i i]
        have hp := posPart_nonneg (v i - v' i)
        change (v i - v' i)⁺ / 2 ≤ (v i - v' i)⁺
        linarith
    obtain ⟨δ₂, hδ₂, hkey⟩ := hex v v' δ₁ hδ₁mem
    have hsumi : ∀ i, v i + v' i = 2 * m i := by
      intro i
      have h := congrFun hsum i
      change v i + v' i = q i + q' i at h
      rw [hmi i]
      linarith
    set w : Fin n → ℝ := δ₁ - δ₂ with hw
    have hboxes : ∀ i, ((lo i ≤ (v - w) i ∧ (v - w) i ≤ hi i) ∧
        (lo i ≤ (v' + w) i ∧ (v' + w) i ≤ hi i)) := by
      intro i
      have h := scalar_box_step (hv_box.1 i) (hv_box.2 i) (hv'_box.1 i) (hv'_box.2 i)
        (hδ₁i i) (hδ₂.1 i) (hδ₂.2 i)
      simpa [hw, Pi.sub_apply, Pi.add_apply] using h
    have hvmem : (v - w, v' + w) ∈ C := by
      refine ⟨⟨⟨⟨fun i => (hboxes i).1.1, fun i => (hboxes i).1.2⟩,
        ⟨fun i => (hboxes i).2.1, fun i => (hboxes i).2.2⟩⟩, ?_⟩, ?_⟩
      · show v - w + (v' + w) = q + q'
        calc
          v - w + (v' + w) = v + v' := by abel
          _ = q + q' := hsum
      · show f (v - w) + f (v' + w) ≤ f q + f q'
        simpa [hw] using hkey.trans hf_le
    have hdist : g₀ (v - w, v' + w) ≤
        g₀ (v, v') - 2 * ∑ i, (v i - m i)⁺ := by
      have hcoord : ∀ i, |(v - w) i - m i| + |(v' + w) i - m i|
          ≤ |v i - m i| + |v' i - m i| - 2 * (v i - m i)⁺ := by
        intro i
        have h := scalar_dist_step (hsumi i) (hδ₁i i) (hδ₂.1 i) (hδ₂.2 i)
        simpa [hw, Pi.sub_apply, Pi.add_apply] using h
      have hsum2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcoord i
      simp only [hg₀, l1Dist, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum] at hsum2 ⊢
      exact hsum2
    have hopt : g₀ (v, v') ≤ g₀ (v - w, v' + w) := hmin hvmem
    have hS : ∑ i, (v i - m i)⁺ ≤ 0 := by linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => show (0 : ℝ) ≤ (v i - m i)⁺ from posPart_nonneg _)).mp
      (le_antisymm hS (Finset.sum_nonneg fun i _ => posPart_nonneg _))
    intro i
    have hz := posPart_eq_zero.mp (hzero i (Finset.mem_univ i))
    linarith
  obtain ⟨⟨⟨hu_box, hu'_box⟩, husum⟩, huf⟩ := humem
  have hu_le : u ≤ m :=
    key u u' ⟨⟨⟨hu_box, hu'_box⟩, husum⟩, huf⟩ humin
  have hswap_mem : (u', u) ∈ C := by
    refine ⟨⟨⟨hu'_box, hu_box⟩, ?_⟩, ?_⟩
    · calc
        u' + u = u + u' := add_comm _ _
        _ = q + q' := husum
    · simpa [add_comm] using huf
  have hswap_min : IsMinOn g₀ C (u', u) := by
    intro p hp
    calc
      g₀ (u', u) = g₀ (u, u') := by simp only [hg₀]; ring
      _ ≤ g₀ p := humin hp
  have hu'_le : u' ≤ m := key u' u hswap_mem hswap_min
  have hueq : u = m := by
    funext i
    have h := congrFun husum i
    change u i + u' i = q i + q' i at h
    have hm_i := hmi i
    linarith [hu_le i, hu'_le i]
  have hu'eq : u' = m := by
    funext i
    have h := congrFun husum i
    change u i + u' i = q i + q' i at h
    have hm_i := hmi i
    rw [hueq] at h
    linarith
  simpa [hm, hueq, hu'eq] using huf

/-- A lower-semicontinuous exchangeable `EReal`-valued function that never
takes `-∞` is convex on the whole finite-dimensional space. -/
theorem convexFunctionOn_univ_of_lsc_exchangeable_ereal {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hbot : ∀ x, f x ≠ ⊥) (hlsc : LowerSemicontinuous f)
    (hex : QOrderE f f) : ConvexFunctionOn Set.univ f := by
  show Convex ℝ (epigraph Set.univ f)
  apply convex_of_isClosed_midpoint_mem
  · exact isClosed_epigraph hlsc
  · rintro ⟨x, r⟩ ⟨-, hxr⟩ ⟨y, s⟩ ⟨-, hys⟩
    have hmid := midpoint_le_of_exchangeable_ereal hbot hlsc hex x y
    let m : Fin n → ℝ := (x + y) / 2
    have hsum : f m + f m ≤ ((r + s : ℝ) : EReal) := by
      calc
        f m + f m ≤ f x + f y := by simpa [m] using hmid
        _ ≤ (r : EReal) + (s : EReal) := add_le_add hxr hys
        _ = ((r + s : ℝ) : EReal) := EReal.coe_add r s
    have hsumtop : f m + f m ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top (r + s)) hsum
    have hmtop : f m ≠ ⊤ := by
      intro hm
      apply hsumtop
      simp [hm]
    lift f m to ℝ using ⟨hmtop, hbot m⟩ with a ha
    have hsum' : a + a ≤ r + s := by
      exact_mod_cast hsum
    refine ⟨Set.mem_univ _, ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
    have harg : (2 : ℝ)⁻¹ • (x + y) = m := by
      ext i
      simp [m, div_eq_mul_inv, mul_comm]
    rw [harg, ← ha]
    apply EReal.coe_le_coe_iff.mpr
    norm_num [smul_eq_mul]
    linarith

/-- **GHS Proposition A.1, full extended-valued form.** A proper,
lower-semicontinuous exchangeable function is proper convex. -/
theorem properConvexOn_univ_of_lsc_exchangeable_ereal {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hbot : ∀ x, f x ≠ ⊥) (hlsc : LowerSemicontinuous f)
    (hproper : ∃ x, f x ≠ ⊤) (hex : QOrderE f f) :
    ProperConvexFunctionOn Set.univ f := by
  refine ⟨convexFunctionOn_univ_of_lsc_exchangeable_ereal hbot hlsc hex, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hproper
    lift f x to ℝ using ⟨hx, hbot x⟩ with r hr
    exact ⟨(x, r), Set.mem_univ _, by rw [hr]⟩
  · intro x _
    exact hbot x

end GHS
