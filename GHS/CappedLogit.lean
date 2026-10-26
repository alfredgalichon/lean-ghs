import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# GHS Phase 6, item 27 (core): the capped-logit water-filling equation

Example `matching_logit` of GHS presents the closed form of the
proposing phase for i.i.d. Gumbel shocks:
`μ_xy = min(μ_x0 · exp α_xy, μ̄_xy)` "where `μ_x0` is defined by
`μ_x0 + Σ_y min(μ_x0 exp α_xy, μ̄_xy) = n_x`".  The implicit claim, that
this scalar water-filling equation has exactly one solution, so the closed
form is well defined, is machine-checked here:

* `exists_unique_capped_root`: for weights `w ≥ 0` (there `w_y = exp α_xy`),
  caps `c ≥ 0` and mass `n ≥ 0`, the map `t ↦ t + Σ_y min(t w_y, c_y)` is
  continuous and strictly increasing with value `0` at `0`, so it crosses
  `n` exactly once (and the root lies in `[0, n]`).

The file first derives the logit response formula by differentiating the
log-sum-exp welfare function along every coordinate and verifies the population
identity for the resulting inside and outside masses.  It then verifies the
algebraic equilibrium step.  If the two sides'
logit response identities hold at nonnegative burn times and at least one burn
time is zero for every pair, then matched mass is the minimum of the two
uncensored logit masses.  Adding the row and column population identities gives
the displayed two-sided system.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set

namespace GHS

/-! ## Log-sum-exp demand -/

/-- The coordinate derivative of log-sum-exp welfare is the corresponding
logit mass.  This is the analytic response identity used in the capped-logit
example. -/
theorem hasDerivAt_logit_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℝ) (U : ι → ℝ) (i : ι) :
    HasDerivAt
      (fun t => n * Real.log (1 + ∑ j, Real.exp (U j + if j = i then t else 0)))
      (n * Real.exp (U i) / (1 + ∑ j, Real.exp (U j))) 0 := by
  classical
  have hterm : ∀ j : ι,
      HasDerivAt (fun t => Real.exp (U j + if j = i then t else 0))
        (if j = i then Real.exp (U j) else 0) 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      have hinner := (hasDerivAt_id 0).const_add (U i)
      have hout := (Real.hasDerivAt_exp (U i)).scomp_of_eq 0 hinner (by simp)
      simpa [Function.comp_def] using hout
    · simpa [hji] using (hasDerivAt_const (x := (0 : ℝ)) (Real.exp (U j)))
  have hsum : HasDerivAt
      (fun t => ∑ j, Real.exp (U j + if j = i then t else 0))
      (Real.exp (U i)) 0 := by
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j) using 1
    all_goals simp
  have hdenom : 0 < 1 + ∑ j, Real.exp (U j) := by
    positivity
  have hlog : HasDerivAt
      (fun t => Real.log (1 + ∑ j, Real.exp (U j + if j = i then t else 0)))
      ((1 + ∑ j, Real.exp (U j))⁻¹ * Real.exp (U i)) 0 := by
    have hinner := (hasDerivAt_const 0 1).add hsum
    have hout := (Real.hasDerivAt_log hdenom.ne').scomp_of_eq 0 hinner (by simp)
    simpa [Function.comp_def, mul_comm] using hout
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlog.const_mul n

/-- Logit outside mass plus all inside masses equals the population. -/
theorem logit_population_identity {ι : Type*} [Fintype ι]
    (n : ℝ) (U : ι → ℝ) :
    n / (1 + ∑ j, Real.exp (U j)) +
        ∑ i, (n / (1 + ∑ j, Real.exp (U j))) * Real.exp (U i) = n := by
  have hdenom : 1 + ∑ j, Real.exp (U j) ≠ 0 := by
    positivity
  rw [← Finset.mul_sum]
  field_simp

/-- **The capped-logit water-filling equation is well posed.** For
nonnegative weights `w`, caps `c`, and mass `n`, there is exactly one
`t ≥ 0` with `t + Σ_y min(t w_y, c_y) = n`; it lies in `[0, n]`. -/
theorem exists_unique_capped_root {ι : Type*} [Fintype ι]
    {w c : ι → ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) {n : ℝ} (hn : 0 ≤ n) :
    ∃! t, 0 ≤ t ∧ t + ∑ y, min (t * w y) (c y) = n := by
  set f : ℝ → ℝ := fun t => t + ∑ y, min (t * w y) (c y) with hf_def
  have hmono : StrictMono f := by
    intro t t' h
    have hsum : ∑ y, min (t * w y) (c y) ≤ ∑ y, min (t' * w y) (c y) :=
      Finset.sum_le_sum fun y _ =>
        min_le_min (mul_le_mul_of_nonneg_right h.le (hw y)) le_rfl
    simp only [hf_def]
    linarith
  have hcont : Continuous f := by
    refine continuous_id.add ?_
    exact continuous_finset_sum _ fun y _ =>
      (continuous_id.mul continuous_const).min continuous_const
  have hf0 : f 0 = 0 := by
    simp only [hf_def, zero_mul, zero_add]
    refine Finset.sum_eq_zero fun y _ => ?_
    exact min_eq_left (hc y)
  have hfn : n ≤ f n := by
    have h : 0 ≤ ∑ y, min (n * w y) (c y) :=
      Finset.sum_nonneg fun y _ => le_min (mul_nonneg hn (hw y)) (hc y)
    simp only [hf_def]
    linarith
  obtain ⟨t, ht_mem, ht⟩ : ∃ t ∈ Icc (0:ℝ) n, f t = n := by
    have hsub := intermediate_value_Icc hn hcont.continuousOn
    have hmem : n ∈ Icc (f 0) (f n) := by
      rw [hf0]
      exact ⟨hn, hfn⟩
    obtain ⟨t, htI, ht⟩ := hsub hmem
    exact ⟨t, htI, ht⟩
  refine ⟨t, ⟨ht_mem.1, ht⟩, ?_⟩
  rintro t' ⟨ht'0, ht'⟩
  exact hmono.injective (ht'.trans ht.symm)

/-! ## The burn-only logit formula -/

/-- A nonnegative burn lowers an uncensored logit mass. -/
theorem mul_exp_sub_le_mul_exp {m a t : ℝ} (hm : 0 ≤ m) (ht : 0 ≤ t) :
    m * Real.exp (a - t) ≤ m * Real.exp a := by
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hm

/-- **Burn-only logit matching formula.** Suppose matched mass satisfies the
logit response identities on both sides at nonnegative burn times.  If the two
burn times are complementary, matched mass is the minimum of the two
uncensored logit masses. -/
theorem burnOnly_logit_matching
    {X Y : Type*} [Fintype X] [Fintype Y]
    {μ α γ τα τγ : X → Y → ℝ} {μx0 : X → ℝ} {μ0y : Y → ℝ}
    (hμx0 : 0 ≤ μx0) (hμ0y : 0 ≤ μ0y)
    (hτα : 0 ≤ τα) (hτγ : 0 ≤ τγ)
    (hG : ∀ x y, μ x y = μx0 x * Real.exp (α x y - τα x y))
    (hH : ∀ x y, μ x y = μ0y y * Real.exp (γ x y - τγ x y))
    (hcomp : ∀ x y, min (τα x y) (τγ x y) = 0) :
    ∀ x y, μ x y = min (μx0 x * Real.exp (α x y))
      (μ0y y * Real.exp (γ x y)) := by
  intro x y
  have hμG : μ x y ≤ μx0 x * Real.exp (α x y) := by
    rw [hG x y]
    exact mul_exp_sub_le_mul_exp (hμx0 x) (hτα x y)
  have hμH : μ x y ≤ μ0y y * Real.exp (γ x y) := by
    rw [hH x y]
    exact mul_exp_sub_le_mul_exp (hμ0y y) (hτγ x y)
  rcases le_total (τα x y) (τγ x y) with hle | hle
  · have ht0 : τα x y = 0 := by
      have := hcomp x y
      rw [min_eq_left hle] at this
      exact this
    have heq : μ x y = μx0 x * Real.exp (α x y) := by
      simpa [ht0] using hG x y
    rw [heq, min_eq_left]
    rwa [← heq]
  · have ht0 : τγ x y = 0 := by
      have := hcomp x y
      rw [min_eq_right hle] at this
      exact this
    have heq : μ x y = μ0y y * Real.exp (γ x y) := by
      simpa [ht0] using hH x y
    rw [heq, min_eq_right]
    rwa [← heq]

/-- The burn-only logit minimum formula and the row and column population
identities imply the paper's two-sided outside-mass system. -/
theorem burnOnly_logit_system
    {X Y : Type*} [Fintype X] [Fintype Y]
    {μ α γ : X → Y → ℝ} {μx0 n : X → ℝ} {μ0y m : Y → ℝ}
    (hmatch : ∀ x y, μ x y = min (μx0 x * Real.exp (α x y))
      (μ0y y * Real.exp (γ x y)))
    (hrow : ∀ x, μx0 x + ∑ y, μ x y = n x)
    (hcol : ∀ y, μ0y y + ∑ x, μ x y = m y) :
    (∀ x, μx0 x + ∑ y, min (μx0 x * Real.exp (α x y))
      (μ0y y * Real.exp (γ x y)) = n x) ∧
    (∀ y, μ0y y + ∑ x, min (μx0 x * Real.exp (α x y))
      (μ0y y * Real.exp (γ x y)) = m y) := by
  constructor
  · intro x
    simpa only [← hmatch] using hrow x
  · intro y
    simpa only [← hmatch] using hcol y

end GHS
