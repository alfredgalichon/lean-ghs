import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real

/-!
# GHS Phase 6, item 27 (core): the capped-logit water-filling equation

Example `matching_logit` of GHS presents the closed form of the
proposing phase for i.i.d. Gumbel shocks:
`μ_xy = min(μ_x0 · exp α_xy, μ̄_xy)` "where `μ_x0` is defined by
`μ_x0 + Σ_y min(μ_x0 exp α_xy, μ̄_xy) = n_x`".  The implicit claim — that
this scalar water-filling equation has exactly one solution, so the closed
form is well defined — is machine-checked here:

* `exists_unique_capped_root` — for weights `w ≥ 0` (there `w_y = exp α_xy`),
  caps `c ≥ 0` and mass `n ≥ 0`, the map `t ↦ t + Σ_y min(t w_y, c_y)` is
  continuous and strictly increasing with value `0` at `0`, so it crosses
  `n` exactly once (and the root lies in `[0, n]`).

The remaining content of the example — that the resulting `μ` is the
argmax of the capped-logit welfare and the two-sided equilibrium system —
is the analytic KKT computation, not formalized here (verified by hand and
numerically in the errata pass).

Mathlib-only (part of the standalone `GHS` target).
-/

open Set

namespace GHS

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

end GHS
