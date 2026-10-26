import GHS.ConjugacyD
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# A strict-epsilon counterexample

The fixed-slack implication written in the submitted appendix is false even
when `D` is the full coordinate set.  Strict inequalities are not preserved
when the conjugate takes a supremum.  This file gives a one-dimensional
closed convex example.  The robust statement quantified over every positive
slack, proved in `ConjugacyD.lean`, is not affected.
-/

open Set

namespace GHS

private def strictEpsDomain : Set (Fin 1 → ℝ) :=
  {q | q 0 ≤ 0}

private theorem strictEpsDomain_convex : Convex ℝ strictEpsDomain := by
  apply convex_halfSpace_le (.mk (by simp) (by simp)) 0

private theorem strictEpsDomain_nonempty : strictEpsDomain.Nonempty := by
  exact ⟨0, by simp [strictEpsDomain]⟩

private theorem strictEpsDomain_closed : IsClosed strictEpsDomain := by
  exact isClosed_le (continuous_apply 0) continuous_const

/-- The indicator of the nonpositive half-line, in one coordinate. -/
noncomputable def strictEpsF (q : Fin 1 → ℝ) : EReal :=
  if q 0 ≤ 0 then 0 else ⊤

/-- Exponential cost on the nonpositive half-line, and `+∞` outside it. -/
noncomputable def strictEpsG (q : Fin 1 → ℝ) : EReal :=
  if q 0 ≤ 0 then (Real.exp (q 0) : EReal) else ⊤

private theorem strictEpsF_eq_indER :
    strictEpsF = indER strictEpsDomain := by
  funext q
  simp [strictEpsF, indER, strictEpsDomain]

private theorem strictEpsG_eq_add_indER (q : Fin 1 → ℝ) :
    strictEpsG q = (Real.exp (q 0) : EReal) + indER strictEpsDomain q := by
  by_cases hq : q 0 ≤ 0 <;> simp [strictEpsG, indER, strictEpsDomain, hq]

/-- The first function in the counterexample is proper convex. -/
theorem strictEpsF_properConvex :
    ProperConvexFunctionOn Set.univ strictEpsF := by
  rw [strictEpsF_eq_indER]
  exact properConvexOn_indER strictEpsDomain_convex strictEpsDomain_nonempty

/-- The first function in the counterexample is lower semicontinuous. -/
theorem strictEpsF_lowerSemicontinuous :
    LowerSemicontinuous strictEpsF := by
  rw [strictEpsF_eq_indER]
  exact lowerSemicontinuous_indER strictEpsDomain_closed

/-- The second function in the counterexample is proper convex. -/
theorem strictEpsG_properConvex :
    ProperConvexFunctionOn Set.univ strictEpsG := by
  have hexp : ConvexOn ℝ strictEpsDomain (fun q : Fin 1 → ℝ => Real.exp (q 0)) := by
    refine ⟨strictEpsDomain_convex, ?_⟩
    intro x _ y _ a b ha hb hab
    simpa only [Pi.add_apply, Pi.smul_apply] using
      convexOn_exp.2 (Set.mem_univ (x 0)) (Set.mem_univ (y 0)) ha hb hab
  refine ⟨?_, ⟨(0, 1), ⟨trivial, ?_⟩⟩, fun q _ => ?_⟩
  · show Convex ℝ (epigraph Set.univ strictEpsG)
    have hset : epigraph (Set.univ : Set (Fin 1 → ℝ)) strictEpsG =
        {p : (Fin 1 → ℝ) × ℝ | p.1 ∈ strictEpsDomain ∧ Real.exp (p.1 0) ≤ p.2} := by
      ext p
      constructor
      · rintro ⟨-, hp⟩
        by_cases hdom : p.1 0 ≤ 0
        · rw [show strictEpsG p.1 = (Real.exp (p.1 0) : EReal) from if_pos hdom] at hp
          exact ⟨hdom, by exact_mod_cast hp⟩
        · rw [show strictEpsG p.1 = ⊤ from if_neg hdom] at hp
          exact absurd (top_le_iff.mp hp) (EReal.coe_ne_top p.2)
      · rintro ⟨hdom, hp⟩
        refine ⟨trivial, ?_⟩
        rw [show strictEpsG p.1 = (Real.exp (p.1 0) : EReal) from if_pos hdom]
        exact_mod_cast hp
    rw [hset]
    exact hexp.convex_epigraph
  · change strictEpsG 0 ≤ ((1 : ℝ) : EReal)
    simp [strictEpsG]
  · unfold strictEpsG
    split <;> simp

/-- The second function in the counterexample is lower semicontinuous. -/
theorem strictEpsG_lowerSemicontinuous :
    LowerSemicontinuous strictEpsG := by
  have hexp : LowerSemicontinuous
      (fun q : Fin 1 → ℝ => (Real.exp (q 0) : EReal)) :=
    ((continuous_coe_real_ereal.comp
      (Real.continuous_exp.comp (continuous_apply 0))).lowerSemicontinuous)
  have hind : LowerSemicontinuous (indER strictEpsDomain) :=
    lowerSemicontinuous_indER strictEpsDomain_closed
  have hadd := hexp.add' hind fun q =>
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  simpa only [← strictEpsG_eq_add_indER] using hadd

@[simp] theorem strictEpsF_ne_top_iff (q : Fin 1 → ℝ) :
    strictEpsF q ≠ ⊤ ↔ q 0 ≤ 0 := by
  simp [strictEpsF]

@[simp] theorem strictEpsG_ne_top_iff (q : Fin 1 → ℝ) :
    strictEpsG q ≠ ⊤ ↔ q 0 ≤ 0 := by
  simp [strictEpsG]

/-- The primal pair satisfies the Q comparison with slack one. -/
theorem strictEps_qOrder :
    QOrderEpsD 1 (Set.univ : Set (Fin 1)) strictEpsF strictEpsG := by
  intro x y hx hy δ₁ hδ₁ _
  have hx0 : x 0 ≤ 0 := (strictEpsF_ne_top_iff x).mp hx
  have hy0 : y 0 ≤ 0 := (strictEpsG_ne_top_iff y).mp hy
  have hd0 : 0 ≤ δ₁ 0 := hδ₁.1 0
  have hd1 : δ₁ 0 ≤ max (x 0 - y 0) 0 := by
    simpa [Pi.sub_apply, posPart] using hδ₁.2 0
  have hxmove : (x - δ₁ + 0) 0 ≤ 0 := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    linarith
  have hymove : (y + δ₁ - 0) 0 ≤ 0 := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    rcases le_total (x 0) (y 0) with hxy | hyx
    · have hmax : max (x 0 - y 0) 0 = 0 := max_eq_right (sub_nonpos.mpr hxy)
      rw [hmax] at hd1
      linarith
    · have hmax : max (x 0 - y 0) 0 = x 0 - y 0 :=
        max_eq_left (sub_nonneg.mpr hyx)
      rw [hmax] at hd1
      linarith
  refine ⟨0, ?_, ?_⟩
  · intro i _
    exact ⟨le_rfl, (negPart_nonneg (x - y)) i⟩
  · rw [show strictEpsF (x - δ₁ + 0) = 0 from if_pos hxmove,
      show strictEpsG (y + δ₁ - 0) = (Real.exp ((y + δ₁ - 0) 0) : EReal) from
        if_pos hymove,
      show strictEpsF x = 0 from if_pos hx0,
      show strictEpsG y = (Real.exp (y 0) : EReal) from if_pos hy0]
    rw [zero_add, zero_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    have hexp_le : Real.exp ((y + δ₁ - 0) 0) ≤ 1 :=
      Real.exp_le_one_iff.mpr hymove
    have hexp_pos : 0 < Real.exp (y 0) := Real.exp_pos _
    linarith

private theorem strictEpsF_conj_zero_le_zero :
    fenchelConjugate 1 strictEpsF 0 ≤ 0 := by
  rw [fenchelConjugate_eq_iSup]
  refine iSup_le fun q => ?_
  by_cases hq : q 0 ≤ 0
  · rw [show strictEpsF q = 0 from if_pos hq, sub_zero]
    simp
  · rw [show strictEpsF q = ⊤ from if_neg hq, EReal.sub_top]
    exact bot_le

private theorem zero_le_strictEpsF_conj_one :
    0 ≤ fenchelConjugate 1 strictEpsF 1 := by
  rw [fenchelConjugate_eq_iSup]
  have h := le_iSup (fun q : Fin 1 → ℝ => ((q ⬝ᵥ (1 : Fin 1 → ℝ) : ℝ) : EReal) -
    strictEpsF q) (0 : Fin 1 → ℝ)
  simpa [strictEpsF, dotProduct] using h

private theorem strictEpsG_conj_one_le_neg_one :
    fenchelConjugate 1 strictEpsG 1 ≤ (-1 : ℝ) := by
  rw [fenchelConjugate_eq_iSup]
  refine iSup_le fun q => ?_
  by_cases hq : q 0 ≤ 0
  · rw [show strictEpsG q = (Real.exp (q 0) : EReal) from if_pos hq,
      ← EReal.coe_sub, EReal.coe_le_coe_iff]
    simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Fin.isValue, Pi.one_apply, mul_one]
    linarith [Real.add_one_le_exp (q 0)]
  · rw [show strictEpsG q = ⊤ from if_neg hq, EReal.sub_top]
    exact bot_le

private theorem neg_one_le_strictEpsG_conj_zero :
    ((-1 : ℝ) : EReal) ≤ fenchelConjugate 1 strictEpsG 0 := by
  rw [fenchelConjugate_eq_iSup]
  have h := le_iSup (fun q : Fin 1 → ℝ => ((q ⬝ᵥ (0 : Fin 1 → ℝ) : ℝ) : EReal) -
    strictEpsG q) (0 : Fin 1 → ℝ)
  simpa [strictEpsG, dotProduct] using h

private theorem strictEpsG_conj_zero_le_zero :
    fenchelConjugate 1 strictEpsG 0 ≤ 0 := by
  rw [fenchelConjugate_eq_iSup]
  refine iSup_le fun q => ?_
  by_cases hq : q 0 ≤ 0
  · rw [show strictEpsG q = (Real.exp (q 0) : EReal) from if_pos hq,
      ← EReal.coe_sub]
    norm_cast
    simp [dotProduct, (Real.exp_pos (q 0)).le]
  · rw [show strictEpsG q = ⊤ from if_neg hq, EReal.sub_top]
    exact bot_le

private theorem zero_le_strictEpsG_conj_zero :
    0 ≤ fenchelConjugate 1 strictEpsG 0 := by
  have hlo := neg_one_le_strictEpsG_conj_zero
  have hhi := strictEpsG_conj_zero_le_zero
  have htop : fenchelConjugate 1 strictEpsG 0 ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top 0) hhi
  have hbot : fenchelConjugate 1 strictEpsG 0 ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-1)) hlo
  lift fenchelConjugate 1 strictEpsG 0 to ℝ using ⟨htop, hbot⟩ with s hs
  change ((0 : ℝ) : EReal) ≤ (s : EReal)
  apply EReal.coe_le_coe_iff.mpr
  by_contra hs0
  have hsneg : s < 0 := lt_of_not_ge hs0
  have hslo : -1 ≤ s := by
    exact EReal.coe_le_coe_iff.mp hlo
  let t : ℝ := -s / 2
  have ht0 : 0 < t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  let q : Fin 1 → ℝ := fun _ => Real.log t
  have hq0 : q 0 ≤ 0 := by
    dsimp [q]
    exact Real.log_nonpos ht0.le ht1
  have hterm := le_iSup
    (fun z : Fin 1 → ℝ => ((z ⬝ᵥ (0 : Fin 1 → ℝ) : ℝ) : EReal) - strictEpsG z) q
  rw [show strictEpsG q = (Real.exp (q 0) : EReal) from if_pos hq0,
    show Real.exp (q 0) = t by simp [q, Real.exp_log ht0],
    show q ⬝ᵥ (0 : Fin 1 → ℝ) = 0 by simp [dotProduct]] at hterm
  have hterm' : ((-t : ℝ) : EReal) ≤ fenchelConjugate 1 strictEpsG 0 := by
    rw [fenchelConjugate_eq_iSup]
    convert hterm using 1
    rw [← EReal.coe_sub]
    congr 2
    ring
  rw [← hs, EReal.coe_le_coe_iff] at hterm'
  dsimp [t] at hterm'
  linarith

/-- The conjugate P comparison with the same slack one fails. -/
theorem not_strictEps_pOrder :
    ¬ POrderEpsD 1 (Set.univ : Set (Fin 1))
      (fenchelConjugate 1 strictEpsG) (fenchelConjugate 1 strictEpsF) := by
  intro hP
  have hcg1 : fenchelConjugate 1 strictEpsG (1 : Fin 1 → ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top (-1)) strictEpsG_conj_one_le_neg_one
  have hcf0 : fenchelConjugate 1 strictEpsF (0 : Fin 1 → ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top 0) strictEpsF_conj_zero_le_zero
  have h := hP 0 1 0 (by simp) (by simp) (by simpa using hcg1) (by simpa using hcf0)
  have hlhs : 0 ≤ fenchelConjugate 1 strictEpsG 0 + fenchelConjugate 1 strictEpsF 1 :=
    add_nonneg zero_le_strictEpsG_conj_zero zero_le_strictEpsF_conj_one
  have hrhs : fenchelConjugate 1 strictEpsG 1 + fenchelConjugate 1 strictEpsF 0 + 1 ≤ 0 := by
    calc
      fenchelConjugate 1 strictEpsG 1 + fenchelConjugate 1 strictEpsF 0 + 1
          ≤ ((-1 : ℝ) : EReal) + 0 + 1 :=
            add_le_add (add_le_add strictEpsG_conj_one_le_neg_one
              strictEpsF_conj_zero_le_zero) le_rfl
      _ = 0 := by
        rw [add_zero]
        change (((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal)) = ((0 : ℝ) : EReal)
        rw [← EReal.coe_add]
        norm_num
  have hnot : ¬ (fenchelConjugate 1 strictEpsG 0 + fenchelConjugate 1 strictEpsF 1 <
      fenchelConjugate 1 strictEpsG 1 + fenchelConjugate 1 strictEpsF 0 + 1) :=
    not_lt_of_ge (hrhs.trans hlhs)
  apply hnot
  simpa using h

/-- Consequently, the same-slack general-`D` implication is false even for
lower-semicontinuous proper convex functions. -/
theorem not_fixed_epsilon_generalD_implication :
    ¬ (∀ {n : ℕ} (D : Set (Fin n)) (f g : (Fin n → ℝ) → EReal) (ε : ℝ),
      LowerSemicontinuous f → ProperConvexFunctionOn Set.univ f →
      LowerSemicontinuous g → ProperConvexFunctionOn Set.univ g →
      0 < ε → QOrderEpsD ε D f g →
        POrderEpsD ε D (fenchelConjugate n g) (fenchelConjugate n f)) := by
  intro h
  exact not_strictEps_pOrder
    (h Set.univ strictEpsF strictEpsG 1 strictEpsF_lowerSemicontinuous
      strictEpsF_properConvex strictEpsG_lowerSemicontinuous strictEpsG_properConvex
      one_pos strictEps_qOrder)

end GHS
