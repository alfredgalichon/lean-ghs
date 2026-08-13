import GHS.BoxCalculus
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Function

/-!
# GHS Phase 3: the corrected Example 1 (§2.1)

The paper's Example 1 is **false as stated** (erratum E1): with the
simplex-constrained entropy, the translate family `ψ = H - ⟨p₀, ·⟩` is *not*
Q-ordered in `p₀`. The corrected example drops the mass constraint, so that
`H*` becomes the *modular* function `p ↦ ∑ z, exp (p z + c z)`. This file
verifies the corrected example on both sides of the duality — without using
the (Phase 4) conjugacy theorem:

* **Primal** (`qOrder_separable_sub_linear`): for any separable cost
  `q ↦ ∑ i, h (q i)` with `h` satisfying the scalar rearrangement inequality
  (any convex function does — `rearrangement_of_convexOn`), the translates by
  `-⟨p₀, ·⟩` are Q-ordered in `p₀`: the exchange succeeds with `δ₂ = 0`.
  This is exactly the corrected Example 1: the (unconstrained) entropy is
  separable convex.
* **Dual** (`pOrder_exp_translate`): the conjugates `p ↦ ∑ i, exp (p i + p₀ i)`
  satisfy the corresponding P-order (with the direction of definition (2.8):
  `ψ ≤_Q ψ'` ↔ `ψ'* ≤_P ψ*`), by the per-coordinate factorization
  `(e^{c'} - e^c)(e^a - e^b) ≥ 0`. In particular each of them is submodular
  (`submodular_exp_translate`).
-/

open Set Finset

namespace GHS

variable {ι : Type*}

/-! ## The scalar rearrangement inequality -/

/-- Any convex function satisfies the rearrangement inequality: moving two
points toward each other (preserving the sum) does not increase the total.
Here `y + δ ≤ x - δ + 2δ = x`, i.e. `0 ≤ δ ≤ x - y`. -/
theorem rearrangement_of_convexOn {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h)
    (x y δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ x - y) :
    h (x - δ) + h (y + δ) ≤ h x + h y := by
  rcases eq_or_lt_of_le (by linarith : y ≤ x) with heq | hlt
  · -- x = y forces δ = 0
    have hδ0' : δ = 0 := le_antisymm (by linarith) hδ0
    simp [hδ0']
  · -- interpolate: x - δ = θx + (1-θ)y and y + δ = (1-θ)x + θy
    set θ : ℝ := 1 - δ / (x - y) with hθ
    have hxy : (0:ℝ) < x - y := by linarith
    have hθ0 : 0 ≤ θ := by
      rw [hθ, sub_nonneg, div_le_one hxy]
      exact hδ
    have hθ1 : θ ≤ 1 := by
      rw [hθ]
      have : 0 ≤ δ / (x - y) := div_nonneg hδ0 hxy.le
      linarith
    have e1 : θ * x + (1 - θ) * y = x - δ := by
      rw [hθ]
      field_simp
      ring
    have e2 : (1 - θ) * x + θ * y = y + δ := by
      rw [hθ]
      field_simp
      ring
    have h1 := hc.2 (mem_univ x) (mem_univ y) hθ0 (by linarith : (0:ℝ) ≤ 1 - θ)
      (by ring : θ + (1 - θ) = 1)
    have h2 := hc.2 (mem_univ x) (mem_univ y) (by linarith : (0:ℝ) ≤ 1 - θ) hθ0
      (by ring : 1 - θ + θ = 1)
    simp only [smul_eq_mul] at h1 h2
    rw [e1] at h1
    rw [e2] at h2
    linarith

/-! ## Primal side: separable costs minus linear translates are Q-ordered -/

/-- **Corrected Example 1, primal form.** If the scalar cost `h` (extended-
real-valued) satisfies the rearrangement inequality, then the separable costs
`ψ(q) = ∑ i, h (q i) - ⟨p₀, q⟩` are Q-ordered along `p₀ ≤ p₀'` — with the
trivial exchange `δ₂ = 0`. -/
theorem qOrder_separable_sub_linear [Fintype ι] (h : ℝ → ERealTop)
    (hre : ∀ x y δ : ℝ, 0 ≤ δ → δ ≤ x - y → h (x - δ) + h (y + δ) ≤ h x + h y)
    {p₀ p₀' : ι → ℝ} (hp : p₀ ≤ p₀') :
    QOrder (fun q => (∑ i, h (q i)) + ((-(p₀ ⬝ᵥ q) : ℝ) : ERealTop))
           (fun q => (∑ i, h (q i)) + ((-(p₀' ⬝ᵥ q) : ℝ) : ERealTop)) := by
  intro q q' δ₁ hδ₁
  refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
  rw [sub_zero]
  -- entropy part: coordinatewise rearrangement
  have hsum : (∑ i, h ((q - δ₁) i)) + ∑ i, h ((q' + δ₁) i)
      ≤ (∑ i, h (q i)) + ∑ i, h (q' i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    show h (q i - δ₁ i) + h (q' i + δ₁ i) ≤ h (q i) + h (q' i)
    by_cases hqi : q' i < q i
    · refine hre (q i) (q' i) (δ₁ i) (hδ₁.1 i) ?_
      have := hδ₁.2 i
      have hpp : (q - q')⁺ i = q i - q' i := by
        rw [posPart_apply, Pi.sub_apply]
        exact posPart_eq_self.mpr (by linarith)
      rw [hpp] at this
      exact this
    · -- q i ≤ q' i forces δ₁ i = 0
      push_neg at hqi
      have hzero : δ₁ i = 0 := by
        have h1 := hδ₁.1 i
        have h2 := hδ₁.2 i
        have hpp : (q - q')⁺ i = 0 := by
          rw [posPart_apply, Pi.sub_apply]
          exact posPart_eq_zero.mpr (by linarith)
        rw [hpp] at h2
        exact le_antisymm h2 h1
      simp [hzero]
  -- linear part: (p₀' - p₀) ⬝ᵥ δ₁ ≥ 0
  have hlin : -(p₀ ⬝ᵥ (q - δ₁)) + -(p₀' ⬝ᵥ (q' + δ₁))
      ≤ -(p₀ ⬝ᵥ q) + -(p₀' ⬝ᵥ q') := by
    rw [dotProduct_sub, dotProduct_add]
    have : (0:ℝ) ≤ p₀' ⬝ᵥ δ₁ - p₀ ⬝ᵥ δ₁ := by
      rw [← sub_dotProduct]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (by have := hp i; simpa [Pi.sub_apply] using sub_nonneg.mpr this)
          (hδ₁.1 i)
    linarith
  -- combine in `WithTop ℝ`
  calc (∑ i, h ((q - δ₁) i)) + ↑(-(p₀ ⬝ᵥ (q - δ₁)))
        + ((∑ i, h ((q' + δ₁) i)) + ↑(-(p₀' ⬝ᵥ (q' + δ₁))))
      = (∑ i, h ((q - δ₁) i)) + ∑ i, h ((q' + δ₁) i)
        + (↑(-(p₀ ⬝ᵥ (q - δ₁))) + ↑(-(p₀' ⬝ᵥ (q' + δ₁)))) := by
        rw [add_add_add_comm]
    _ ≤ (∑ i, h (q i)) + ∑ i, h (q' i) + (↑(-(p₀ ⬝ᵥ q)) + ↑(-(p₀' ⬝ᵥ q'))) := by
        refine add_le_add hsum ?_
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
        exact hlin
    _ = (∑ i, h (q i)) + ↑(-(p₀ ⬝ᵥ q)) + ((∑ i, h (q' i)) + ↑(-(p₀' ⬝ᵥ q'))) := by
        rw [add_add_add_comm]

/-! ## Dual side: translates of the modular conjugate are P-ordered -/

/-- Per-coordinate inequality behind the dual side: for `c ≤ c'`,
`e^{min a b + c'} + e^{max a b + c} ≤ e^{a + c'} + e^{b + c}`, by the
factorization `(e^{c'} - e^c)(e^a - e^b) ≥ 0`. -/
theorem exp_translate_coord (a b c c' : ℝ) (hcc : c ≤ c') :
    Real.exp (min a b + c') + Real.exp (max a b + c)
      ≤ Real.exp (a + c') + Real.exp (b + c) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hab, max_eq_left hab]
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
    have h2 : Real.exp c ≤ Real.exp c' := Real.exp_le_exp.mpr hcc
    have h3 : Real.exp b ≤ Real.exp a := Real.exp_le_exp.mpr hab
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h3)]

/-- **Corrected Example 1, dual form.** For `p₀ ≤ p₀'`, the translated modular
conjugates satisfy `ψ'* ≤_P ψ*` where `ψ*(p) = ∑ i, exp (p i + p₀ i)` — the
direction required by definition (2.8) for `ψ ≤_Q ψ'`. -/
theorem pOrder_exp_translate [Fintype ι] {p₀ p₀' : ι → ℝ} (hp : p₀ ≤ p₀') :
    POrder (fun p : ι → ℝ => ((∑ i, Real.exp (p i + p₀' i) : ℝ) : ERealTop))
           (fun p : ι → ℝ => ((∑ i, Real.exp (p i + p₀ i) : ℝ) : ERealTop)) := by
  intro p p'
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  show Real.exp ((p ⊓ p') i + p₀' i) + Real.exp ((p ⊔ p') i + p₀ i)
      ≤ Real.exp (p i + p₀' i) + Real.exp (p' i + p₀ i)
  rw [show (p ⊓ p') i = min (p i) (p' i) from rfl,
    show (p ⊔ p') i = max (p i) (p' i) from rfl]
  exact exp_translate_coord (p i) (p' i) (p₀ i) (p₀' i) (hp i)

/-- The modular conjugate `p ↦ ∑ i, exp (p i + p₀ i)` is submodular. -/
theorem submodular_exp_translate [Fintype ι] (p₀ : ι → ℝ) :
    Submodular (fun p : ι → ℝ => ((∑ i, Real.exp (p i + p₀ i) : ℝ) : ERealTop)) :=
  pOrder_exp_translate (le_refl p₀)

end GHS
