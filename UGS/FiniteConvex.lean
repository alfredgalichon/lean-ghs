import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Finite-dimensional convex analysis for UGS

This file contains the small real-valued convex-analysis interface needed by
GSV Theorem 3.  It deliberately avoids the external Rockafellar formalization:
all functions are finite and defined on the whole Euclidean space `Fin n → ℝ`.
-/

open Filter Matrix

namespace Correspondence

variable {n : ℕ}

/-- A vector subgradient of a finite real-valued function. -/
def SubgradVec (f : (Fin n → ℝ) → ℝ) (p q : Fin n → ℝ) : Prop :=
  ∀ x, f p + q ⬝ᵥ (x - p) ≤ f x

/-- The subdifferential, viewed as a correspondence of vectors. -/
def subdiffCorr (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → Prop :=
  fun p q => SubgradVec f p q

/-- The right directional derivative of `f` at `p` in direction `b`. -/
noncomputable def dderiv (f : (Fin n → ℝ) → ℝ) (p b : Fin n → ℝ) : ℝ :=
  derivWithin (fun t : ℝ => f (p + t • b)) (Set.Ioi 0) 0

/-- Restricting a convex function to an affine line preserves convexity. -/
theorem convexOn_line (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (p b : Fin n → ℝ) :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun t : ℝ => f (p + t • b)) := by
  have h := hconv.comp_affineMap (AffineMap.lineMap p (p + b))
  have hset : (AffineMap.lineMap p (p + b) : ℝ →ᵃ[ℝ] (Fin n → ℝ)) ⁻¹'
      (Set.univ : Set (Fin n → ℝ)) = Set.univ := by simp
  have hfun : (f ∘ (AffineMap.lineMap p (p + b) : ℝ →ᵃ[ℝ] (Fin n → ℝ))) =
      (fun t : ℝ => f (p + t • b)) := by
    funext t
    simp only [Function.comp_apply]
    congr 1
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left, add_comm]
  rwa [hset, hfun] at h

/-- The right directional derivative is the infimum of positive secant slopes. -/
theorem dderiv_eq_sInf_slope (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (p b : Fin n → ℝ) :
    dderiv f p b =
      sInf (slope (fun t : ℝ => f (p + t • b)) 0 '' Set.Ioi (0 : ℝ)) := by
  rw [dderiv]
  have hline := convexOn_line f hconv p b
  have h := hline.rightDeriv_eq_sInf_slope_of_mem_interior
    (x := (0 : ℝ)) (by simp)
  simpa only [Set.mem_univ, true_and] using h

/-- Positive secant slopes converge to the right directional derivative. -/
theorem tendsto_slope_dderiv (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (p b : Fin n → ℝ) :
    Filter.Tendsto (slope (fun t : ℝ => f (p + t • b)) 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (dderiv f p b)) := by
  have hder := (convexOn_line f hconv p b).hasDerivWithinAt_rightDeriv_of_mem_interior
    (x := (0 : ℝ)) (by simp)
  simpa only [dderiv, Set.diff_singleton_eq_self (Set.notMem_Ioi_self)] using
    (hasDerivWithinAt_iff_tendsto_slope.mp hder)

/-- Multiplication by a positive constant preserves the right-neighbourhood filter at zero. -/
theorem tendsto_pos_mul_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ => a * t) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa only [mul_zero] using
      (show ContinuousAt (fun t : ℝ => a * t) 0 by fun_prop).tendsto.mono_left
        (show nhdsWithin 0 (Set.Ioi 0) ≤ nhds 0 by exact inf_le_left)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos ha ht

/-- The directional derivative is positively homogeneous in its direction. -/
theorem dderiv_pos_smul (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (p b : Fin n → ℝ) {a : ℝ} (ha : 0 < a) :
    dderiv f p (a • b) = a * dderiv f p b := by
  let A : ℝ → ℝ := fun t => f (p + t • b)
  have hA : HasDerivWithinAt A (dderiv f p b) (Set.Ioi 0) 0 := by
    exact (convexOn_line f hconv p b).hasDerivWithinAt_rightDeriv_of_mem_interior
      (x := (0 : ℝ)) (by simp)
  have hmul : HasDerivWithinAt (fun t : ℝ => a * t) a (Set.Ioi 0) 0 :=
    (hasDerivAt_const_mul (x := (0 : ℝ)) a).hasDerivWithinAt
  have hA0 : HasDerivWithinAt A (dderiv f p b) (Set.Ioi 0) (a * 0) := by
    simpa only [mul_zero] using hA
  have hcomp := hA0.comp 0 hmul (fun _ ht => mul_pos ha ht)
  have hscaled : HasDerivWithinAt (fun t : ℝ => f (p + t • (a • b)))
      (dderiv f p b * a) (Set.Ioi 0) 0 := by
    simpa only [A, Function.comp_apply, smul_smul, mul_comm] using hcomp
  have h := hscaled.derivWithin (uniqueDiffWithinAt_Ioi (0 : ℝ))
  simpa only [dderiv, mul_comm] using h

/-- The directional derivative in the zero direction vanishes. -/
theorem dderiv_zero (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) : dderiv f p 0 = 0 := by
  simp [dderiv]

/-- The directional derivative is subadditive in its direction. -/
theorem dderiv_add_le (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (p b c : Fin n → ℝ) :
    dderiv f p (b + c) ≤ dderiv f p b + dderiv f p c := by
  let A : ℝ → ℝ := fun t => f (p + t • (b + c))
  let B : ℝ → ℝ := fun t => f (p + t • b)
  let C : ℝ → ℝ := fun t => f (p + t • c)
  have hA : Tendsto (slope A 0) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (dderiv f p (b + c))) := tendsto_slope_dderiv f hconv p (b + c)
  have hscale : Tendsto (fun t : ℝ => 2 * t) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := tendsto_pos_mul_nhdsGT_zero (by norm_num)
  have hB : Tendsto (fun t => slope B 0 (2 * t)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (dderiv f p b)) := (tendsto_slope_dderiv f hconv p b).comp hscale
  have hC : Tendsto (fun t => slope C 0 (2 * t)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (dderiv f p c)) := (tendsto_slope_dderiv f hconv p c).comp hscale
  apply le_of_tendsto_of_tendsto hA (hB.add hC)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hconvex := hconv.2
    (show p + (2 * t) • b ∈ (Set.univ : Set (Fin n → ℝ)) by simp)
    (show p + (2 * t) • c ∈ (Set.univ : Set (Fin n → ℝ)) by simp)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hpoint :
      (1 / 2 : ℝ) • (p + (2 * t) • b) + (1 / 2 : ℝ) • (p + (2 * t) • c) =
        p + t • (b + c) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hpoint] at hconvex
  simp only [smul_eq_mul] at hconvex
  dsimp only [A, B, C]
  rw [slope_def_field, slope_def_field, slope_def_field]
  simp only [zero_smul, add_zero, sub_zero]
  apply (div_le_iff₀ ht).2
  have hrhs : t * ((f (p + (2 * t) • b) - f p) / (2 * t) +
      (f (p + (2 * t) • c) - f p) / (2 * t)) =
      ((f (p + (2 * t) • b) - f p) + (f (p + (2 * t) • c) - f p)) / 2 := by
    field_simp [ht0.ne']
  rw [mul_comm _ t, hrhs]
  nlinarith [hconvex]

/-- Every positive secant slope dominates the right directional derivative. -/
theorem dderiv_le_quotient (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (p b : Fin n → ℝ)
    {t : ℝ} (ht : 0 < t) :
    dderiv f p b ≤ (f (p + t • b) - f p) / t := by
  rw [dderiv_eq_sInf_slope f hconv]
  have hbdd : BddBelow
      (slope (fun s : ℝ => f (p + s • b)) 0 '' Set.Ioi (0 : ℝ)) := by
    simpa only [Set.mem_univ, true_and] using
      bddBelow_slope_lt_of_mem_interior (convexOn_line f hconv p b)
        (x := (0 : ℝ)) (by simp)
  have hmem : slope (fun s : ℝ => f (p + s • b)) 0 t ∈
      slope (fun s : ℝ => f (p + s • b)) 0 '' Set.Ioi (0 : ℝ) := ⟨t, ht, rfl⟩
  refine (csInf_le hbdd hmem).trans_eq ?_
  rw [slope_def_field]
  simp

/-- A subgradient is dominated by every directional derivative. -/
theorem subgrad_le_dderiv (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    {p q : Fin n → ℝ} (hq : SubgradVec f p q) (b : Fin n → ℝ) :
    q ⬝ᵥ b ≤ dderiv f p b := by
  rw [dderiv_eq_sInf_slope f hconv]
  apply le_csInf
  · exact ⟨slope (fun t : ℝ => f (p + t • b)) 0 1, 1, (show (0 : ℝ) < 1 by norm_num), rfl⟩
  rintro _ ⟨t, ht, rfl⟩
  have hsub := hq (p + t • b)
  have ht0 : 0 ≤ t := ht.le
  have hdot : q ⬝ᵥ ((p + t • b) - p) = t * (q ⬝ᵥ b) := by
    rw [add_sub_cancel_left]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot] at hsub
  rw [slope_def_field]
  simp only [zero_smul, add_zero, sub_zero]
  apply (le_div_iff₀ ht).2
  linarith

/-- Hahn--Banach selects a subgradient attaining the directional derivative in a
prescribed direction.  This is the finite, full-domain form of the support part
of Rockafellar's Theorem 23.4 needed by GSV. -/
theorem exists_subgrad_achieving (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (p d : Fin n → ℝ) :
    ∃ q : Fin n → ℝ, SubgradVec f p q ∧ dderiv f p d = q ⬝ᵥ d := by
  let D : (Fin n → ℝ) → ℝ := fun b => dderiv f p b
  have hzero : D 0 = 0 := dderiv_zero f p
  have hcompat : ∀ c : ℝ, c • d = 0 → c • D d = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · simp [hc0]
    have hd0 : d = 0 := (smul_eq_zero.mp hc).resolve_left hc0
    simp [hd0, hzero]
  let L : (Fin n → ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' d (D d) hcompat
  have hdom : ∀ x : L.domain, L x ≤ D x := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [LinearPMap.mkSpanSingleton'_apply]
    by_cases hcpos : 0 < c
    · exact le_of_eq (dderiv_pos_smul f hconv p d hcpos).symm
    by_cases hc0 : c = 0
    · subst c
      simp [D, dderiv_zero]
    have hcneg : c < 0 := lt_of_le_of_ne (not_lt.mp hcpos) hc0
    have hsum := dderiv_add_le f hconv p (c • d) ((-c) • d)
    have hcancel : c • d + (-c) • d = (0 : Fin n → ℝ) := by
      rw [← add_smul]
      simp
    rw [hcancel, dderiv_zero, dderiv_pos_smul f hconv p d (neg_pos.mpr hcneg)] at hsum
    dsimp only [D]
    simp only [smul_eq_mul]
    linarith
  obtain ⟨g, hgL, hgD⟩ := exists_extension_of_le_sublinear L D
    (fun c hc b => dderiv_pos_smul f hconv p b hc)
    (fun b c => dderiv_add_le f hconv p b c) hdom
  let q : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g
  have hqdot : ∀ b : Fin n → ℝ, q ⬝ᵥ b = g b := by
    intro b
    change (dotProductEquiv ℝ (Fin n) q) b = g b
    rw [show dotProductEquiv ℝ (Fin n) q = g by
      exact LinearEquiv.apply_symm_apply (dotProductEquiv ℝ (Fin n)) g]
  have hqd : g d = D d := by
    have hdmem : d ∈ L.domain := by
      change d ∈ Submodule.span ℝ {d}
      exact Submodule.mem_span_singleton_self d
    have h := hgL ⟨d, hdmem⟩
    rw [LinearPMap.mkSpanSingleton'_apply_self] at h
    exact h
  refine ⟨q, ?_, ?_⟩
  · intro x
    have hlinear : q ⬝ᵥ (x - p) ≤ D (x - p) := by
      rw [hqdot]
      exact hgD (x - p)
    have hsec := dderiv_le_quotient f hconv p (x - p) (t := (1 : ℝ)) one_pos
    have hsec' : D (x - p) ≤ f x - f p := by
      simpa only [D, one_smul, add_sub_cancel, div_one] using hsec
    linarith
  · rw [hqdot, hqd]

/-- A subdifferential is convex. -/
theorem subdiffVec_convex (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) :
    Convex ℝ {q | SubgradVec f p q} := by
  intro q hq r hr a b ha hb hab
  intro x
  have hqx := hq x
  have hrx := hr x
  have hdot : (a • q + b • r) ⬝ᵥ (x - p) =
      a * (q ⬝ᵥ (x - p)) + b * (r ⬝ᵥ (x - p)) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  rw [hdot]
  calc
    f p + (a * (q ⬝ᵥ (x - p)) + b * (r ⬝ᵥ (x - p))) =
        (a + b) * f p + (a * (q ⬝ᵥ (x - p)) + b * (r ⬝ᵥ (x - p))) := by
          rw [hab]
          ring
    _ =
        a * (f p + q ⬝ᵥ (x - p)) + b * (f p + r ⬝ᵥ (x - p)) := by
          ring
    _ ≤ a * f x + b * f x :=
      add_le_add (mul_le_mul_of_nonneg_left hqx ha) (mul_le_mul_of_nonneg_left hrx hb)
    _ = f x := by rw [← add_mul, hab, one_mul]

/-- A subdifferential is closed. -/
theorem subdiffVec_closed (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) :
    IsClosed {q | SubgradVec f p q} := by
  have hset : {q | SubgradVec f p q} =
      ⋂ x, {q : Fin n → ℝ | f p + q ⬝ᵥ (x - p) ≤ f x} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter, SubgradVec]
  rw [hset]
  refine isClosed_iInter fun x => isClosed_le ?_ continuous_const
  exact continuous_const.add (by fun_prop)

/-- Subgradients of a finite function on the whole space are coordinatewise bounded. -/
theorem subdiffVec_bounded (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) :
    Bornology.IsBounded {q | SubgradVec f p q} := by
  let e : Fin n → Fin n → ℝ := fun i => Pi.single i 1
  let lo : Fin n → ℝ := fun i => f p - f (p - e i)
  let hi : Fin n → ℝ := fun i => f (p + e i) - f p
  have hsubset : {q | SubgradVec f p q} ⊆ Set.pi Set.univ (fun i => Set.Icc (lo i) (hi i)) := by
    intro q hq
    rw [Set.mem_pi]
    intro i _
    rw [Set.mem_Icc]
    have hplus := hq (p + e i)
    have hminus := hq (p - e i)
    have hdotPlus : q ⬝ᵥ ((p + e i) - p) = q i := by
      rw [add_sub_cancel_left]
      simpa [e] using dotProduct_single_one q i
    have hdotMinus : q ⬝ᵥ ((p - e i) - p) = -q i := by
      have heq : (p - e i) - p = -e i := by abel
      rw [heq, dotProduct_neg]
      simpa [e] using congrArg Neg.neg (dotProduct_single_one q i)
    rw [hdotPlus] at hplus
    rw [hdotMinus] at hminus
    constructor <;> dsimp [lo, hi] <;> linarith
  exact (Bornology.IsBounded.pi fun i => Metric.isBounded_Icc (lo i) (hi i)).subset hsubset

/-- A subdifferential is compact in finite dimension. -/
theorem subdiffVec_compact (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) :
    IsCompact {q | SubgradVec f p q} :=
  Metric.isCompact_of_isClosed_isBounded (subdiffVec_closed f p) (subdiffVec_bounded f p)

end Correspondence
