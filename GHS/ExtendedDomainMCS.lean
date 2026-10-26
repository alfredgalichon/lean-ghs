import GHS.Conjugacy
import UGS.ProfitDomainRI

/-!
# Extended-valued submodularity from relative subgradient monotonicity

This file bridges the real-valued domain theorem in `UGS.ProfitDomainRI` to a
closed proper convex function taking values in `EReal`.  It isolates the
extended-domain step used in the converse direction of the GHS rejected-
quantity comparative-statics theorem.
-/

open Set

namespace GHS

variable {n : ℕ}

local notation "V" => Fin n → ℝ

/-- The real-valued restriction of an extended-real function to its effective
domain.  Its values away from the effective domain are immaterial. -/
noncomputable def finitePart (φ : V → EReal) : V → ℝ := fun x => (φ x).toReal

/-- On the effective domain, a proper extended-real function is the coercion
of its finite part. -/
theorem coe_finitePart_of_mem {φ : V → EReal}
    (hbot : ∀ x, φ x ≠ ⊥) {x : V} (hx : x ∈ effectiveDomain Set.univ φ) :
    ((finitePart φ x : ℝ) : EReal) = φ x := by
  exact EReal.coe_toReal (ne_of_lt hx.2) (hbot x)

/-- Convexity of an extended-real function becomes ordinary convexity after
restriction to its effective domain. -/
theorem convexOn_finitePart {φ : V → EReal} (hφ : ConvexFunction φ)
    (hbot : ∀ x, φ x ≠ ⊥) :
    ConvexOn ℝ (effectiveDomain Set.univ φ) (finitePart φ) := by
  refine convexOn_of_convex_epigraph ?_
  have hset :
      {p : V × ℝ | p.1 ∈ effectiveDomain Set.univ φ ∧ finitePart φ p.1 ≤ p.2}
        = epigraph Set.univ φ := by
    ext p
    constructor
    · rintro ⟨hp, hle⟩
      refine ⟨Set.mem_univ _, ?_⟩
      rw [← coe_finitePart_of_mem hbot hp]
      exact_mod_cast hle
    · rintro ⟨-, hle⟩
      have htop : φ p.1 ≠ ⊤ := by
        exact ne_top_of_le_ne_top (EReal.coe_ne_top p.2) hle
      have hp : p.1 ∈ effectiveDomain Set.univ φ :=
        ⟨Set.mem_univ _, lt_top_iff_ne_top.mpr htop⟩
      refine ⟨hp, ?_⟩
      rw [← coe_finitePart_of_mem hbot hp] at hle
      exact_mod_cast hle
  rw [hset]
  exact hφ

/-- Lower semicontinuity is likewise inherited by the real-valued restriction
to the effective domain. -/
theorem lowerSemicontinuousOn_finitePart {φ : V → EReal}
    (hlsc : LowerSemicontinuous φ) (hbot : ∀ x, φ x ≠ ⊥) :
    LowerSemicontinuousOn (finitePart φ) (effectiveDomain Set.univ φ) := by
  intro x hx y hy
  have hcoe : (y : EReal) < φ x := by
    rw [← coe_finitePart_of_mem hbot hx]
    exact EReal.coe_lt_coe_iff.mpr hy
  have hev := (hlsc.lowerSemicontinuousOn (effectiveDomain Set.univ φ)) x hx
    (y : EReal) hcoe
  filter_upwards [hev, self_mem_nhdsWithin] with x' hx' hx'D
  rw [← coe_finitePart_of_mem hbot hx'D] at hx'
  exact EReal.coe_lt_coe_iff.mp hx'

/-- Submodularity of the finite part on a sublattice effective domain is
exactly the extended-real P-inequality; pairs outside the domain are automatic. -/
theorem pOrderE_of_submodularOn_finitePart {φ : V → EReal}
    (hbot : ∀ x, φ x ≠ ⊥)
    (hDl : Correspondence.IsPriceSublattice (effectiveDomain Set.univ φ))
    (hsub : Correspondence.SubmodularOnSet (effectiveDomain Set.univ φ)
      (finitePart φ)) : POrderE φ φ := by
  intro x y
  by_cases hx : x ∈ effectiveDomain Set.univ φ
  · by_cases hy : y ∈ effectiveDomain Set.univ φ
    · obtain ⟨hmeet, hjoin⟩ := hDl hx hy
      have h := hsub hx hy
      rw [← coe_finitePart_of_mem hbot hmeet,
        ← coe_finitePart_of_mem hbot hjoin,
        ← coe_finitePart_of_mem hbot hx,
        ← coe_finitePart_of_mem hbot hy,
        ← EReal.coe_add, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr h
    · have hytop : φ y = ⊤ := by
        simp only [effectiveDomain, Set.mem_univ, true_and] at hy
        exact not_lt_top_iff.mp hy
      rw [hytop, EReal.add_top_of_ne_bot (hbot x)]
      exact le_top
  · have hxtop : φ x = ⊤ := by
      simp only [effectiveDomain, Set.mem_univ, true_and] at hx
      exact not_lt_top_iff.mp hx
    rw [hxtop, EReal.top_add_of_ne_bot (hbot y)]
    exact le_top

/-- **Extended-domain converse, analytic core.** Let `φ` be a closed proper
convex extended-real function whose effective domain is a sublattice.  If its
relative subdifferential satisfies the weak Kelso--Crawford pair condition on
the relative interior of the domain, then `φ` is submodular in the extended-
real sense.

This removes the finite-valued restriction from the previously formalized
subgradient-to-submodularity implication. -/
theorem pOrderE_of_KCpairOn_intrinsicInterior {φ : V → EReal}
    (hproper : ProperConvexFunctionOn Set.univ φ)
    (hlsc : LowerSemicontinuous φ)
    (hDl : Correspondence.IsPriceSublattice (effectiveDomain Set.univ φ))
    (hpair : Correspondence.KCpairOn (effectiveDomain Set.univ φ)
      (intrinsicInterior ℝ (effectiveDomain Set.univ φ)) (finitePart φ)) :
    POrderE φ φ := by
  let D := effectiveDomain Set.univ φ
  let f := finitePart φ
  have hbot : ∀ x, φ x ≠ ⊥ := fun x => hproper.2.2 x (Set.mem_univ x)
  have hf : ConvexOn ℝ D f := convexOn_finitePart hproper.1 hbot
  have hD : Convex ℝ D := hf.1
  have hlscf : LowerSemicontinuousOn f D :=
    lowerSemicontinuousOn_finitePart hlsc hbot
  have hPl : Correspondence.IsPriceSublattice (intrinsicInterior ℝ D) :=
    Correspondence.ri_sublattice hD hDl
  have hne : ∀ p ∈ intrinsicInterior ℝ D, ∃ s, Correspondence.SubgradOn D f p s :=
    fun p hp => Correspondence.exists_subgrad_of_mem_ri hD hf hp
  have hall := Correspondence.theorem3_domain hD hDl hf hlscf hPl
    (fun _ h => h) intrinsicInterior_subset hne
  have hsub : Correspondence.SubmodularOnSet D f := (hall.out 5 0).mp hpair
  exact pOrderE_of_submodularOn_finitePart hbot hDl hsub

end GHS
