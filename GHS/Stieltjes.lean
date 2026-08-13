import GHS.BoxCalculus
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# GHS Phase 3: the Stieltjes characterization (§2.2)

`GHS.dotProduct_mulVec_posPart_nonneg_iff` formalizes the quadratic-case
characterization of GHS §2.2: for a matrix `Q`,

  `∀ x, 0 ≤ x ⬝ᵥ Q *ᵥ x⁺`  ⟺  `Q` is positive semidefinite (as a quadratic
  form) and has nonpositive off-diagonal entries.

The paper states this for symmetric invertible `Q` ("Q is a Stieltjes matrix
iff `(p'-p)ᵀ Q (p'-p)⁺ ≥ 0` for all `p, p'`"); the version here is sharper —
no symmetry is needed, and positive *semi*definiteness is the exact content
(with `Q` invertible, PSD upgrades to PD, recovering the Stieltjes class).

Proof ingredients, as in the hand verification:
* (⟸) split `x = x⁺ - x⁻`; the cross term `x⁻ ⬝ᵥ Q *ᵥ x⁺` is a sum of
  nonpositive terms — diagonal terms vanish by `posPart_mul_negPart`,
  off-diagonal terms have sign `(+)·(-)·(+)`.
* (⟹, off-diagonal) test on `x = t·e_i - e_j` with `t = Q j i / (2(Q i i + 1))`.
* (⟹, PSD) for a Z-matrix the quadratic form dominates its absolute-value
  form: `|x| ⬝ᵥ Q *ᵥ |x| ≤ x ⬝ᵥ Q *ᵥ x`, and `|x| = |x|⁺` reduces to the
  hypothesis.
-/

open Finset

namespace GHS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Expansion of the quadratic-type pairing as a double sum. -/
theorem dotProduct_mulVec_eq_sum (Q : Matrix ι ι ℝ) (x y : ι → ℝ) :
    x ⬝ᵥ Q.mulVec y = ∑ i, ∑ j, x i * (Q i j * y j) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]

/-- **GHS §2.2.** `x ⬝ᵥ Q *ᵥ x⁺ ≥ 0` for all `x` iff `Q` is positive
semidefinite and has nonpositive off-diagonal entries. -/
theorem dotProduct_mulVec_posPart_nonneg_iff (Q : Matrix ι ι ℝ) :
    (∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ Q.mulVec x⁺) ↔
      ((∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ Q.mulVec x) ∧ ∀ i j, i ≠ j → Q i j ≤ 0) := by
  constructor
  · intro h
    -- diagonal entries are nonnegative: test on x = e_i
    have hdiag : ∀ i, 0 ≤ Q i i := by
      intro i
      have hsingle : ((Pi.single i 1 : ι → ℝ))⁺ = (Pi.single i 1 : ι → ℝ) := by
        funext k
        show ((Pi.single i 1 : ι → ℝ) k)⁺ = (Pi.single i 1 : ι → ℝ) k
        refine posPart_eq_self.mpr ?_
        by_cases hk : k = i <;> simp [Pi.single_apply, hk]
      have hv := h (Pi.single i 1 : ι → ℝ)
      rw [hsingle] at hv
      simpa [Matrix.mulVec_single, single_dotProduct] using hv
    -- off-diagonal entries are nonpositive: test on x = t·e_i - e_j
    have hoff : ∀ i j, i ≠ j → Q i j ≤ 0 := by
      intro i j hij
      by_contra hpos
      push_neg at hpos
      -- the transposed test vector isolates Q i j: x = t·e_j - e_i
      set t : ℝ := Q i j / (2 * (Q j j + 1)) with ht
      have hQjj := hdiag j
      have htpos : 0 < t := div_pos hpos (by linarith)
      set x : ι → ℝ := t • (Pi.single j 1 : ι → ℝ) - (Pi.single i 1 : ι → ℝ) with hx
      have hxplus : x⁺ = t • (Pi.single j 1 : ι → ℝ) := by
        funext k
        show (x k)⁺ = (t • (Pi.single j 1 : ι → ℝ)) k
        by_cases hkj : k = j
        · have hxk : x k = t := by
            simp [hx, hkj, Ne.symm hij]
          rw [hxk, posPart_eq_self.mpr htpos.le]
          simp [hkj]
        · by_cases hki : k = i
          · have hxk : x k = -1 := by
              simp [hx, hki, hij]
            rw [hxk, posPart_eq_zero.mpr (by norm_num)]
            simp [hkj]
          · have hxk : x k = 0 := by
              simp [hx, hkj, hki]
            rw [hxk, posPart_eq_zero.mpr le_rfl]
            simp [hkj]
      have hv := h x
      rw [hxplus] at hv
      have hval : x ⬝ᵥ Q.mulVec (t • (Pi.single j 1 : ι → ℝ))
          = t * (t * Q j j) - t * Q i j := by
        simp [hx, Matrix.mulVec_smul, Matrix.mulVec_single, sub_dotProduct,
          smul_dotProduct, single_dotProduct, smul_eq_mul]
        ring
      rw [hval] at hv
      -- 0 ≤ t·(t·Q j j - Q i j) with t = Q i j / (2(Q j j + 1)) is absurd
      have habs : Q i j ≤ t * Q j j := by nlinarith
      have ht2 : t * Q j j < Q i j := by
        rw [ht]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (Q j j + 1))]
        nlinarith
      linarith
    refine ⟨?_, hoff⟩
    -- PSD: compare the quadratic form with its absolute-value version
    intro y
    set ay : ι → ℝ := fun k => |y k| with hay
    have hayplus : ay⁺ = ay := by
      funext k
      show (ay k)⁺ = ay k
      exact posPart_eq_self.mpr (abs_nonneg _)
    have h0 : 0 ≤ ay ⬝ᵥ Q.mulVec ay := by
      have := h ay
      rwa [hayplus] at this
    have hcompare : ay ⬝ᵥ Q.mulVec ay ≤ y ⬝ᵥ Q.mulVec y := by
      rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum]
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      by_cases hij : i = j
      · subst hij
        have heq : ay i * (Q i i * ay i) = y i * (Q i i * y i) := by
          calc ay i * (Q i i * ay i) = Q i i * (|y i| * |y i|) := by
                simp only [hay]; ring
            _ = Q i i * (y i * y i) := by rw [abs_mul_abs_self]
            _ = y i * (Q i i * y i) := by ring
        rw [heq]
      · have hQ := hoff i j hij
        have h1 : y i * y j ≤ |y i| * |y j| := by
          calc y i * y j ≤ |y i * y j| := le_abs_self _
            _ = |y i| * |y j| := abs_mul _ _
        have h2 : (0:ℝ) ≤ |y i| * |y j| - y i * y j := by linarith
        simp only [hay]
        nlinarith [mul_nonneg (neg_nonneg.mpr hQ) h2]
    linarith
  · rintro ⟨hpsd, hoff⟩ x
    -- decompose x = x⁺ - x⁻ and control the cross term
    have hdecomp : x = x⁺ - x⁻ := by
      funext k
      show x k = (x k)⁺ - (x k)⁻
      exact (posPart_sub_negPart (x k)).symm
    have hcross : x⁻ ⬝ᵥ Q.mulVec x⁺ ≤ 0 := by
      rw [dotProduct_mulVec_eq_sum]
      refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
      by_cases hij : i = j
      · subst hij
        have h0 : (x i)⁺ * (x i)⁻ = 0 := posPart_mul_negPart (x i)
        have : x⁻ i * (Q i i * x⁺ i) = Q i i * ((x i)⁺ * (x i)⁻) := by
          simp only [posPart_apply, negPart_apply]
          ring
        rw [this, h0, mul_zero]
      · have h1 : (0:ℝ) ≤ x⁻ i := negPart_nonneg (x i)
        have h2 : Q i j ≤ 0 := hoff i j hij
        have h3 : (0:ℝ) ≤ x⁺ j := posPart_nonneg (x j)
        have : x⁻ i * (Q i j * x⁺ j) = Q i j * (x⁻ i * x⁺ j) := by ring
        rw [this]
        exact mul_nonpos_of_nonpos_of_nonneg h2 (mul_nonneg h1 h3)
    have hmain : x ⬝ᵥ Q.mulVec x⁺ = x⁺ ⬝ᵥ Q.mulVec x⁺ - x⁻ ⬝ᵥ Q.mulVec x⁺ := by
      conv_rhs => rw [← sub_dotProduct, ← hdecomp]
    rw [hmain]
    have := hpsd x⁺
    -- x⁺ ⬝ᵥ Q *ᵥ x⁺ needs (x⁺)⁺ = x⁺? no: hpsd is the raw form, applies directly
    linarith

end GHS
