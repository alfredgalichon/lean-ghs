import GHS.ExtendedFenchel
import GHS.PriceMCS

/-!
# Capacity-constrained rejections for an extended-valued conjugate
-/

open Set

namespace GHS

variable {n : ℕ}

local notation "V" => Fin n → ℝ

/-- Every capacity objective is bounded below by the Fenchel--Young constant. -/
theorem extendedCapacityObjective_ge {φ : V → EReal}
    (hproper : ProperConvexFunctionOn Set.univ φ)
    {p : V} (hp : p ∈ effectiveDomain Set.univ φ) (qb u : V) :
    ((p ⬝ᵥ qb - finitePart φ p : ℝ) : ERealTop) ≤
      extendedDualCostTop φ hproper (qb - u) +
        ((p ⬝ᵥ u : ℝ) : ERealTop) := by
  have hbot : ∀ x, φ x ≠ ⊥ := fun x => hproper.2.2 x (Set.mem_univ x)
  have hcost : ((p ⬝ᵥ (qb - u) - finitePart φ p : ℝ) : ERealTop) ≤
      extendedDualCostTop φ hproper (qb - u) := by
    rw [← toE_le_toE, toE_coe, toE_extendedDualCostTop,
      fenchelConjugate_eq_iSup]
    calc
      ((p ⬝ᵥ (qb - u) - finitePart φ p : ℝ) : EReal) =
          ((p ⬝ᵥ (qb - u) : ℝ) : EReal) - φ p := by
            rw [← coe_finitePart_of_mem hbot hp, ← EReal.coe_sub]
      _ ≤ ⨆ x : V, ((x ⬝ᵥ (qb - u) : ℝ) : EReal) - φ x :=
        le_iSup (fun x : V => ((x ⬝ᵥ (qb - u) : ℝ) : EReal) - φ x) p
  calc
    ((p ⬝ᵥ qb - finitePart φ p : ℝ) : ERealTop) =
        ((p ⬝ᵥ (qb - u) - finitePart φ p : ℝ) : ERealTop) +
          ((p ⬝ᵥ u : ℝ) : ERealTop) := by
            rw [← WithTop.coe_add]
            congr 1
            rw [dotProduct_sub]
            ring
    _ ≤ extendedDualCostTop φ hproper (qb - u) +
          ((p ⬝ᵥ u : ℝ) : ERealTop) := add_le_add hcost le_rfl

/-- At a relative subgradient, the capacity objective attains its
Fenchel--Young lower bound. -/
theorem extendedCapacityObjective_eq_of_subgradOn {φ : V → EReal}
    (hproper : ProperConvexFunctionOn Set.univ φ)
    {p : V} (hp : p ∈ effectiveDomain Set.univ φ) {qb z : V}
    (hz : Correspondence.SubgradOn (effectiveDomain Set.univ φ)
      (finitePart φ) p z) :
    extendedDualCostTop φ hproper (qb - (qb - z)) +
        ((p ⬝ᵥ (qb - z) : ℝ) : ERealTop) =
      ((p ⬝ᵥ qb - finitePart φ p : ℝ) : ERealTop) := by
  rw [show qb - (qb - z) = z by abel,
    extendedDualCostTop_eq_of_subgradOn hproper hp hz, ← WithTop.coe_add]
  congr 1
  rw [dotProduct_sub]
  ring

/-- Rejected bundles for the conjugate of an extended-real function. -/
def extendedSubdiffRejections (φ : V → EReal)
    (hproper : ProperConvexFunctionOn Set.univ φ) (p qb : V) : Set V :=
  argminOn (fun u => extendedDualCostTop φ hproper (qb - u) +
    ((p ⬝ᵥ u : ℝ) : ERealTop)) {v | 0 ≤ v}

/-- Provided a feasible relative subgradient exists, rejection minimizers are
exactly the complements of feasible relative subgradients. -/
theorem mem_extendedSubdiffRejections_iff {φ : V → EReal}
    (hproper : ProperConvexFunctionOn Set.univ φ)
    {p : V} (hp : p ∈ effectiveDomain Set.univ φ) {qb z₀ u : V}
    (hz₀ : Correspondence.SubgradOn (effectiveDomain Set.univ φ)
      (finitePart φ) p z₀) (hz₀qb : z₀ ≤ qb) :
    u ∈ extendedSubdiffRejections φ hproper p qb ↔
      0 ≤ u ∧ Correspondence.SubgradOn (effectiveDomain Set.univ φ)
        (finitePart φ) p (qb - u) := by
  let obj : V → ERealTop := fun v =>
    extendedDualCostTop φ hproper (qb - v) + ((p ⬝ᵥ v : ℝ) : ERealTop)
  let K : ERealTop := ((p ⬝ᵥ qb - finitePart φ p : ℝ) : ERealTop)
  have hlower (v : V) : K ≤ obj v := extendedCapacityObjective_ge hproper hp qb v
  have hvalue {z : V}
      (hz : Correspondence.SubgradOn (effectiveDomain Set.univ φ)
        (finitePart φ) p z) : obj (qb - z) = K := by
    dsimp [obj, K]
    exact extendedCapacityObjective_eq_of_subgradOn hproper hp hz
  constructor
  · rintro ⟨hu, hmin⟩
    have hv₀ : 0 ≤ qb - z₀ := by intro i; dsimp; linarith [hz₀qb i]
    have hobj : obj u = K :=
      le_antisymm (by rw [← hvalue hz₀]; exact hmin (qb - z₀) hv₀) (hlower u)
    have hcostEq : extendedDualCostTop φ hproper (qb - u) =
        ((p ⬝ᵥ (qb - u) - finitePart φ p : ℝ) : ERealTop) := by
      apply le_antisymm
      · have hadd :
            extendedDualCostTop φ hproper (qb - u) +
                ((p ⬝ᵥ u : ℝ) : ERealTop) ≤
              ((p ⬝ᵥ (qb - u) - finitePart φ p : ℝ) : ERealTop) +
                ((p ⬝ᵥ u : ℝ) : ERealTop) := by
          change obj u ≤ _
          rw [hobj]
          change ((p ⬝ᵥ qb - finitePart φ p : ℝ) : ERealTop) ≤ _
          rw [← WithTop.coe_add]
          apply le_of_eq
          congr 1
          rw [dotProduct_sub]
          ring
        exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp hadd
      · rw [← toE_le_toE, toE_coe, toE_extendedDualCostTop,
          fenchelConjugate_eq_iSup]
        have hbot : ∀ x, φ x ≠ ⊥ :=
          fun x => hproper.2.2 x (Set.mem_univ x)
        calc
          ((p ⬝ᵥ (qb - u) - finitePart φ p : ℝ) : EReal) =
              ((p ⬝ᵥ (qb - u) : ℝ) : EReal) - φ p := by
                rw [← coe_finitePart_of_mem hbot hp, ← EReal.coe_sub]
          _ ≤ ⨆ x : V, ((x ⬝ᵥ (qb - u) : ℝ) : EReal) - φ x :=
            le_iSup (fun x : V => ((x ⬝ᵥ (qb - u) : ℝ) : EReal) - φ x) p
    have hcostE : fenchelConjugate n φ (qb - u) =
        ((p ⬝ᵥ (qb - u) - finitePart φ p : ℝ) : EReal) := by
      rw [← toE_extendedDualCostTop hproper (qb - u), hcostEq, toE_coe]
    exact ⟨hu, (subgradOn_iff_fenchelConjugate_eq hproper hp (qb - u)).mpr hcostE⟩
  · rintro ⟨hu, hz⟩
    refine ⟨hu, fun v _ => ?_⟩
    change obj u ≤ obj v
    rw [show obj u = K by
      have he := hvalue hz
      rw [show qb - (qb - u) = u by abel] at he
      exact he]
    exact hlower v

end GHS
