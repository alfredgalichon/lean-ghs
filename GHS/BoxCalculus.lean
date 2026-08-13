import GHS.Orders
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# GHS Phase 1: box and positive-part calculus

The small arithmetic facts that the later monotone-comparative-statics proofs
lean on (roadmap Phase 1, item 4):

* `Icc_posPart_subset`, `negPart_le_of_le` — if `v ≤ w` then
  `[0, v⁺] ⊆ [0, w⁺]` and `w⁻ ≤ v⁻`.  These are the two box comparisons used
  in the proof of Theorem 2, (1) ⟹ (4): with `a = q̄ - u`, `a' = q̄' - u'` and
  `q̄ ≤ q̄'` one has `u - u' ≤ a' - a`, hence
  `[0, (u-u')⁺] ⊆ [0, (a'-a)⁺]` and `(a'-a)⁻ ≤ (u-u')⁻`.
* `posPart_mul_negPart` — pointwise complementarity `a⁺ * a⁻ = 0` on `ℝ`.
* `isGreatest_boxDot_posPart` — for `y ≥ 0`,
  `sup { sᵀx : 0 ≤ s ≤ y } = yᵀ(x⁺)`, attained at `s* = y·𝟙{x > 0}`
  (the identity "`yᵀx⁺ = sup_{0 ≤ s ≤ y} sᵀx`" of GHS §2.2, used in the
  quadratic characterization of exchangeability).

Mathlib already supplies the underlying monotonicity (`posPart_mono`,
`negPart_anti`) and the decomposition `posPart_sub_negPart : a⁺ - a⁻ = a`;
this file only packages them in the forms the paper's proofs consume.
-/

open Set Finset

namespace GHS

variable {ι : Type*}

/-- Monotonicity of the positive part on `ι → ℝ`, pointwise. -/
theorem posPart_le_posPart {v w : ι → ℝ} (h : v ≤ w) : v⁺ ≤ w⁺ :=
  fun i => posPart_mono (h i)

/-- If `v ≤ w` then `[0, v⁺] ⊆ [0, w⁺]` (GHS proof of Thm 2, (1)⟹(4)). -/
theorem Icc_posPart_subset {v w : ι → ℝ} (h : v ≤ w) :
    Icc (0 : ι → ℝ) v⁺ ⊆ Icc 0 w⁺ :=
  Icc_subset_Icc le_rfl (posPart_le_posPart h)

/-- If `v ≤ w` then `w⁻ ≤ v⁻`: a `δ₂` produced in the larger box `[0, w⁻]`
is admissible in the smaller box `[0, v⁻]` (GHS proof of Thm 2, (1)⟹(4)). -/
theorem negPart_le_of_le {v w : ι → ℝ} (h : v ≤ w) : w⁻ ≤ v⁻ :=
  fun i => negPart_anti (h i)

/-- Complementarity of the parts, in product form on `ℝ`: `a⁺ * a⁻ = 0`. -/
theorem posPart_mul_negPart (a : ℝ) : a⁺ * a⁻ = 0 := by
  rcases le_or_gt a 0 with ha | ha
  · rw [posPart_eq_zero.mpr ha, zero_mul]
  · rw [negPart_eq_zero.mpr ha.le, mul_zero]

/-- The optimal transfer in a box: for `y ≥ 0`, the linear form `s ↦ ∑ i, s i * x i`
attains its maximum over the box `[0, y]` at `s* = y·𝟙{x > 0}`, with value
`∑ i, y i * (x i)⁺`.  This is the identity `yᵀx⁺ = sup_{0 ≤ s ≤ y} sᵀx`
of GHS §2.2. -/
theorem isGreatest_boxDot_posPart [Fintype ι] (x y : ι → ℝ) (hy : 0 ≤ y) :
    IsGreatest ((fun s => ∑ i, s i * x i) '' Icc 0 y) (∑ i, y i * (x i)⁺) := by
  constructor
  · -- attained at s* = y·𝟙{x > 0}
    refine ⟨fun i => if 0 < x i then y i else 0, ⟨?_, ?_⟩, ?_⟩
    · intro i
      show (0 : ℝ) ≤ if 0 < x i then y i else 0
      by_cases hi : 0 < x i
      · rw [if_pos hi]; exact hy i
      · rw [if_neg hi]
    · intro i
      show (if 0 < x i then y i else 0) ≤ y i
      by_cases hi : 0 < x i
      · rw [if_pos hi]
      · rw [if_neg hi]; exact hy i
    · refine Finset.sum_congr rfl fun i _ => ?_
      show (if 0 < x i then y i else 0) * x i = y i * (x i)⁺
      by_cases hi : 0 < x i
      · rw [if_pos hi, posPart_eq_self.mpr hi.le]
      · push_neg at hi
        rw [if_neg (not_lt.mpr hi), posPart_eq_zero.mpr hi, zero_mul, mul_zero]
  · -- upper bound: s i * x i ≤ y i * (x i)⁺ coordinatewise
    rintro v ⟨s, hs, rfl⟩
    refine Finset.sum_le_sum fun i _ => ?_
    rcases le_or_gt 0 (x i) with hx | hx
    · rw [posPart_eq_self.mpr hx]
      exact mul_le_mul_of_nonneg_right (hs.2 i) hx
    · rw [posPart_eq_zero.mpr hx.le, mul_zero]
      nlinarith [mul_nonneg (hs.1 i) (neg_nonneg.mpr hx.le)]

end GHS
