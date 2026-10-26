import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# GSV Lemma 6 (`huddle`): submodularity as a discrete lattice inequality

This file formalizes **Lemma 6** of Galichon–Samuelson–Vernet — the pure
lattice-theoretic spine of Theorem 3's convex-analysis half (`c*` submodular
⟺ `∂c*` satisfies UGS).

For a function `f : (ι → α) → α` on the product lattice, submodularity
`f (p ⊓ p') + f (p ⊔ p') ≤ f p + f p'` is *equivalent* to the "huddle"
inequality: for every pair `p, p'` and every `b ≥ 0` with `b^{>} ≤ (p - p')⁺`,
```
    f (p + b^{≤}) + f (p' + b^{>}) + f (p ⊓ p') ≤ f p + f p' + f (p ⊓ p' + b),
```
where `b^{≤}` (`borderLe`) keeps `b_z` on coordinates with `p_z ≤ p'_z` and zeroes
the rest, and `b^{>}` (`borderGt`) keeps `b_z` where `p_z > p'_z`.

The proof is entirely elementary — submodularity applied to two well-chosen
pairs, plus the coordinatewise meet/join identities
`p ⊔ (p ⊓ p' + b) = p + b^{≤}`, `p ⊓ (p ⊓ p' + b) = p ⊓ p' + b^{>}`,
`(p ⊓ p' + b^{>}) ⊓ p' = p ⊓ p'`, `(p ⊓ p' + b^{>}) ⊔ p' = p' + b^{>}`.

*Scope.* This is the one self-contained brick of GSV's Appendix A.7. The rest of
Theorem 3 (i)⟺(ii) — Lemmas `char-subdiff`, `tympani`, `diffcstartilde`,
`diff-char-submod` — is the duality between the subdifferential and one-sided
directional derivatives (Rockafellar Thms 13.1, 23.4, the supporting-hyperplane
theorem), which is *not* currently available in Mathlib and is deferred. What is
machine-checked here is that submodularity is exactly the combinatorial content
that feeds that duality. The complementary half, that the profit-max supply is
automatically nonreversing (Theorem 3 (ii)⟺(iii)), is in `UGS/ProfitMax.lean`.

Setup: `[Field α] [LinearOrder α] [IsStrictOrderedRing α]` (only the lattice-ordered additive-group
structure is used; the field is a convenience so `linarith`/`ring` apply).
-/

namespace Correspondence

variable {ι : Type*} {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- A function on the product lattice `ι → α` is **submodular** when
`f (p ⊓ p') + f (p ⊔ p') ≤ f p + f p'` for all `p, p'`. -/
def Submodular (f : (ι → α) → α) : Prop :=
  ∀ p p', f (p ⊓ p') + f (p ⊔ p') ≤ f p + f p'

/-- `b^{≤}` (GSV eq. (border)): keeps `b_z` on coordinates where `p_z ≤ p'_z`,
zero elsewhere. -/
def borderLe (p p' b : ι → α) : ι → α := fun z => if p z ≤ p' z then b z else 0

/-- `b^{>}` (GSV eq. (border)): keeps `b_z` on coordinates where `p_z > p'_z`,
zero elsewhere. -/
def borderGt (p p' b : ι → α) : ι → α := fun z => if p z ≤ p' z then 0 else b z

/-- Coordinatewise identity `p ⊔ (p ⊓ p' + b) = p + b^{≤}` (needs `b ≥ 0` and
`b^{>} ≤ (p - p')⁺`). -/
theorem sup_meet_add (p p' b : ι → α) (hb : ∀ z, 0 ≤ b z)
    (hbgt : ∀ z, p' z < p z → b z ≤ p z - p' z) :
    p ⊔ (p ⊓ p' + b) = p + borderLe p p' b := by
  funext z
  simp only [Pi.sup_apply, Pi.add_apply, Pi.inf_apply, borderLe]
  by_cases hz : p z ≤ p' z
  · rw [inf_of_le_left hz, if_pos hz]
    exact sup_of_le_right (le_add_of_nonneg_right (hb z))
  · have hlt : p' z < p z := not_le.mp hz
    rw [inf_of_le_right hlt.le, if_neg hz, add_zero]
    exact sup_of_le_left (by have := hbgt z hlt; linarith)

/-- Coordinatewise identity `p ⊓ (p ⊓ p' + b) = p ⊓ p' + b^{>}` (needs `b ≥ 0`
and `b^{>} ≤ (p - p')⁺`). -/
theorem inf_meet_add (p p' b : ι → α) (hb : ∀ z, 0 ≤ b z)
    (hbgt : ∀ z, p' z < p z → b z ≤ p z - p' z) :
    p ⊓ (p ⊓ p' + b) = p ⊓ p' + borderGt p p' b := by
  funext z
  simp only [Pi.inf_apply, Pi.add_apply, borderGt]
  by_cases hz : p z ≤ p' z
  · rw [if_pos hz, inf_of_le_left hz, add_zero]
    exact inf_of_le_left (le_add_of_nonneg_right (hb z))
  · have hlt : p' z < p z := not_le.mp hz
    rw [if_neg hz, inf_of_le_right hlt.le]
    exact inf_of_le_right (by have := hbgt z hlt; linarith)

/-- Coordinatewise identity `(p ⊓ p' + b^{>}) ⊓ p' = p ⊓ p'`. -/
theorem inf_meetGt (p p' b : ι → α) (hb : ∀ z, 0 ≤ b z) :
    (p ⊓ p' + borderGt p p' b) ⊓ p' = p ⊓ p' := by
  funext z
  simp only [Pi.inf_apply, Pi.add_apply, borderGt]
  by_cases hz : p z ≤ p' z
  · rw [if_pos hz, add_zero]
    exact inf_of_le_left inf_le_right
  · have hlt : p' z < p z := not_le.mp hz
    rw [if_neg hz, inf_of_le_right hlt.le]
    exact inf_of_le_right (le_add_of_nonneg_right (hb z))

/-- Coordinatewise identity `(p ⊓ p' + b^{>}) ⊔ p' = p' + b^{>}`. -/
theorem sup_meetGt (p p' b : ι → α) (hb : ∀ z, 0 ≤ b z) :
    (p ⊓ p' + borderGt p p' b) ⊔ p' = p' + borderGt p p' b := by
  funext z
  simp only [Pi.sup_apply, Pi.add_apply, Pi.inf_apply, borderGt]
  by_cases hz : p z ≤ p' z
  · rw [if_pos hz, add_zero, add_zero]
    exact sup_of_le_right inf_le_right
  · have hlt : p' z < p z := not_le.mp hz
    rw [if_neg hz, inf_of_le_right hlt.le]
    exact sup_of_le_left (le_add_of_nonneg_right (hb z))

/-- The **huddle inequality** (GSV Lemma 6, the inequality side): for all `p, p'`
and `b ≥ 0` with `b^{>} ≤ (p - p')⁺`,
`f (p + b^{≤}) + f (p' + b^{>}) + f (p ⊓ p') ≤ f p + f p' + f (p ⊓ p' + b)`. -/
def HuddleIneq (f : (ι → α) → α) : Prop :=
  ∀ p p' b : ι → α, 0 ≤ b → (∀ z, p' z < p z → b z ≤ p z - p' z) →
    f (p + borderLe p p' b) + f (p' + borderGt p p' b) + f (p ⊓ p')
      ≤ f p + f p' + f (p ⊓ p' + b)

/-- **GSV Lemma 6 (`huddle`).** A function `f : (ι → α) → α` is submodular if and
only if it satisfies the huddle inequality. -/
theorem submodular_iff_huddle (f : (ι → α) → α) : Submodular f ↔ HuddleIneq f := by
  constructor
  · -- Submodular ⟹ huddle: apply submodularity twice and combine.
    intro hf p p' b hb0 hbgt
    have hb : ∀ z, 0 ≤ b z := fun z => by simpa using (Pi.le_def.mp hb0 z)
    have H1 := hf p (p ⊓ p' + b)
    rw [inf_meet_add p p' b hb hbgt, sup_meet_add p p' b hb hbgt] at H1
    have H2 := hf (p ⊓ p' + borderGt p p' b) p'
    rw [inf_meetGt p p' b hb, sup_meetGt p p' b hb] at H2
    linarith
  · -- Huddle ⟹ submodular: specialize at `b = (p' - p) ⊔ 0`.
    intro hH p p'
    set b : ι → α := (p' - p) ⊔ 0 with hbdef
    have hb0 : (0 : ι → α) ≤ b := by rw [hbdef]; exact le_sup_right
    have hbgt : ∀ z, p' z < p z → b z ≤ p z - p' z := by
      intro z hz
      simp only [hbdef, Pi.sup_apply, Pi.sub_apply, Pi.zero_apply]
      exact sup_le (by linarith) (by linarith)
    have hbb : p ⊓ p' + b = p' := by
      funext z
      simp only [hbdef, Pi.add_apply, Pi.inf_apply, Pi.sup_apply, Pi.sub_apply, Pi.zero_apply]
      by_cases hz : p z ≤ p' z
      · rw [inf_of_le_left hz, sup_of_le_left (by linarith : (0 : α) ≤ p' z - p z)]; linarith
      · have hlt : p' z < p z := not_le.mp hz
        rw [inf_of_le_right hlt.le, sup_of_le_right (by linarith : p' z - p z ≤ (0 : α))]; linarith
    have hbl : p + borderLe p p' b = p ⊔ p' := by
      funext z
      simp only [hbdef, Pi.add_apply, Pi.sup_apply, Pi.sub_apply, Pi.zero_apply, borderLe]
      by_cases hz : p z ≤ p' z
      · rw [if_pos hz, sup_of_le_left (by linarith : (0 : α) ≤ p' z - p z), sup_of_le_right hz]
        linarith
      · have hlt : p' z < p z := not_le.mp hz
        rw [if_neg hz, sup_of_le_left hlt.le]; linarith
    have hbg : p' + borderGt p p' b = p' := by
      funext z
      simp only [hbdef, Pi.add_apply, borderGt, Pi.sup_apply, Pi.sub_apply, Pi.zero_apply]
      by_cases hz : p z ≤ p' z
      · rw [if_pos hz]; linarith
      · have hlt : p' z < p z := not_le.mp hz
        rw [if_neg hz, sup_of_le_right (by linarith : p' z - p z ≤ (0 : α))]; linarith
    have key := hH p p' b hb0 hbgt
    rw [hbb, hbl, hbg] at key
    linarith

end Correspondence
