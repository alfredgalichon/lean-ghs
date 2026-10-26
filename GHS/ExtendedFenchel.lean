import GHS.ExtendedDomainMCS

/-!
# Fenchel--Young theory on an effective domain

This file identifies relative subgradients of the finite part of a proper
extended-real convex function with maximizers of its conjugate objective.
-/

open Set

namespace GHS

variable {n : ℕ}

local notation "V" => Fin n → ℝ

/-- The conjugate of a proper extended-real function, represented in
`WithTop ℝ`; properness ensures that the conjugate never takes `-∞`. -/
noncomputable def extendedDualCostTop (φ : V → EReal)
    (hproper : ProperConvexFunctionOn Set.univ φ) (q : V) : ERealTop :=
  (fenchelConjugate n φ q).unbot (fenchelConjugate_ne_bot_of_proper hproper q)

private theorem toE_eq_withBotCoe_extended (a : ERealTop) :
    toE a = WithBot.some a := by
  induction a using WithTop.recTopCoe with
  | top => rfl
  | coe r => rfl

@[simp] theorem toE_extendedDualCostTop {φ : V → EReal}
    (hproper : ProperConvexFunctionOn Set.univ φ) (q : V) :
    toE (extendedDualCostTop φ hproper q) = fenchelConjugate n φ q := by
  rw [toE_eq_withBotCoe_extended]
  exact WithBot.coe_unbot _ _

/-- Fenchel--Young equality for a relative subgradient on the effective
domain. -/
theorem subgradOn_iff_fenchelConjugate_eq {φ : V → EReal}
    (hproper : ProperConvexFunctionOn Set.univ φ)
    {p : V} (hp : p ∈ effectiveDomain Set.univ φ) (z : V) :
    Correspondence.SubgradOn (effectiveDomain Set.univ φ) (finitePart φ) p z ↔
      fenchelConjugate n φ z = ((p ⬝ᵥ z - finitePart φ p : ℝ) : EReal) := by
  have hbot : ∀ x, φ x ≠ ⊥ := fun x => hproper.2.2 x (Set.mem_univ x)
  constructor
  · intro hz
    rw [fenchelConjugate_eq_iSup]
    apply le_antisymm
    · refine iSup_le fun x => ?_
      by_cases hx : x ∈ effectiveDomain Set.univ φ
      · have hreal : x ⬝ᵥ z - finitePart φ x ≤ p ⬝ᵥ z - finitePart φ p := by
          have h := hz x hx
          rw [dotProduct_sub] at h
          rw [dotProduct_comm z x, dotProduct_comm z p] at h
          linarith
        rw [← coe_finitePart_of_mem hbot hx, ← EReal.coe_sub]
        exact EReal.coe_le_coe_iff.mpr hreal
      · have hxtop : φ x = ⊤ := by
          simp only [effectiveDomain, Set.mem_univ, true_and] at hx
          exact not_lt_top_iff.mp hx
        simp [hxtop]
    · calc
        ((p ⬝ᵥ z - finitePart φ p : ℝ) : EReal) =
            ((p ⬝ᵥ z : ℝ) : EReal) - φ p := by
              rw [← coe_finitePart_of_mem hbot hp, ← EReal.coe_sub]
        _ ≤ ⨆ x : V, ((x ⬝ᵥ z : ℝ) : EReal) - φ x :=
          le_iSup (fun x : V => ((x ⬝ᵥ z : ℝ) : EReal) - φ x) p
  · intro hz x hx
    have hterm : ((x ⬝ᵥ z : ℝ) : EReal) - φ x ≤ fenchelConjugate n φ z := by
      rw [fenchelConjugate_eq_iSup]
      exact le_iSup (fun y : V => ((y ⬝ᵥ z : ℝ) : EReal) - φ y) x
    rw [hz, ← coe_finitePart_of_mem hbot hx, ← EReal.coe_sub] at hterm
    have hreal := EReal.coe_le_coe_iff.mp hterm
    rw [dotProduct_comm x z, dotProduct_comm p z] at hreal
    rw [dotProduct_sub]
    linarith

/-- At a relative subgradient, the transported `WithTop` cost has the
Fenchel--Young value. -/
theorem extendedDualCostTop_eq_of_subgradOn {φ : V → EReal}
    (hproper : ProperConvexFunctionOn Set.univ φ)
    {p : V} (hp : p ∈ effectiveDomain Set.univ φ) {z : V}
    (hz : Correspondence.SubgradOn (effectiveDomain Set.univ φ)
      (finitePart φ) p z) :
    extendedDualCostTop φ hproper z =
      ((p ⬝ᵥ z - finitePart φ p : ℝ) : ERealTop) := by
  apply le_antisymm
  · rw [← toE_le_toE, toE_extendedDualCostTop, toE_coe,
      (subgradOn_iff_fenchelConjugate_eq hproper hp z).mp hz]
  · rw [← toE_le_toE, toE_extendedDualCostTop, toE_coe,
      (subgradOn_iff_fenchelConjugate_eq hproper hp z).mp hz]

end GHS
