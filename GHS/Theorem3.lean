import GHS.Proposition3
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# GHS Phase 6: Theorem 3, limit identification (τ-free form)

The convergence content of GHS Theorem 3 at the level of the matching masses,
bypassing the waiting-time (`τ`) decomposition: along the convergent
subsequence extracted in `GHS/DeferredAcceptance.lean`, the common limit `μ`
of proposals and tentative acceptances satisfies

* `theorem3_limit` (G-side): `Ainf - μ` is an optimal rejection at the
  limiting capacity `Ainf` — i.e. `μ ∈ M^G(α, Ainf)` in the paper's
  acceptance variables; and (H-side) `0 ∈ rejectSet_H γ μ` — **nothing is
  rejected at `μ`**: `μ` is a fixed point of the disposal phase,
  `μ ∈ M^H(γ, μ)`.  These are the two membership claims of the paper's proof
  of Theorem 3 (`μ ∈ M^G(α, μ^A)` and `μ ∈ M^H(γ, μ)`); the further
  decomposition into waiting times (KKT multipliers) is the remaining,
  separate step.

Ingredients, both elementary thanks to the algorithm's structure:

* `rejectSet_limit_antitone` — the rejection correspondence has closed graph
  along **monotone** capacities: because `Ainf ≤ A k`, any acceptance
  feasible in the limit is feasible at every round, so optimality passes to
  the limit by continuity of the cost on `D` (no lower hemicontinuity
  needed).
* `rejectSet_fixedPoint_of_tendsto` — for the H-side the capacities
  `P (φ k)` converge but not monotonically; feasibility in the limit is
  recovered by scaling: for `ν ∈ D` with `ν ≤ μ` and `θ < 1`, `θ • ν` is
  eventually feasible (`μ i = 0` forces `ν i = 0` since `D` sits in the
  nonnegative orthant; `μ i > 0` gives room).  This needs `D` convex with
  `0 ∈ D` — satisfied by the paper's `D = dom H*` (a conjugate's domain)
  and already part of the `WelfareDual` bundle except for convexity, taken
  here as a hypothesis.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set Filter Topology

namespace GHS

namespace WelfareDual

variable {ι : Type*} [Fintype ι] (W : WelfareDual ι)

/-- The acceptance objective `ν ↦ cost ν - ⟨p, ν⟩`: minimizing it over
`{ν ∈ D | ν ≤ qb}` is the acceptance form of the rejection problem. -/
def aobj (p : ι → ℝ) : (ι → ℝ) → ℝ := fun ν => W.cost ν - p ⬝ᵥ ν

theorem mem_feas_iff {qb v : ι → ℝ} :
    v ∈ W.feas qb ↔ 0 ≤ v ∧ qb - v ∈ W.D := by
  constructor
  · rintro ⟨h0, μ, hμ, rfl⟩
    refine ⟨h0, ?_⟩
    have h : qb - (qb - μ) = μ := by abel
    rwa [h]
  · rintro ⟨h0, hD⟩
    exact ⟨h0, qb - v, hD, by abel⟩

theorem mem_rejectSet_iff {p qb r : ι → ℝ} (hqb : 0 ≤ qb) :
    r ∈ W.rejectSet p qb ↔
      r ∈ W.feas qb ∧ ∀ v ∈ W.feas qb, W.robj p qb r ≤ W.robj p qb v := by
  obtain ⟨u₀, hu₀, heq, hmin⟩ := W.rejectSet_eq p qb hqb
  rw [heq]
  constructor
  · rintro ⟨hrf, hrle⟩
    exact ⟨hrf, fun v hv => le_trans hrle (hmin hv)⟩
  · rintro ⟨hrf, hopt⟩
    exact ⟨hrf, hopt u₀ hu₀⟩

theorem robj_eq_aobj_add {p qb v : ι → ℝ} :
    W.robj p qb v = W.aobj p (qb - v) + p ⬝ᵥ qb := by
  rw [robj, aobj, dotProduct_sub]
  ring

/-- The rejection problem in acceptance variables: `r` is an optimal
rejection at capacity `qb` iff the accepted mass `qb - r` lies in `D` and
minimizes `cost ν - ⟨p, ν⟩` over `{ν ∈ D | ν ≤ qb}`. -/
theorem mem_rejectSet_iff_acceptance {p qb r : ι → ℝ} (hqb : 0 ≤ qb) :
    r ∈ W.rejectSet p qb ↔
      0 ≤ r ∧ qb - r ∈ W.D ∧
        ∀ ν ∈ W.D, ν ≤ qb → W.aobj p (qb - r) ≤ W.aobj p ν := by
  rw [W.mem_rejectSet_iff hqb]
  constructor
  · rintro ⟨hrf, hopt⟩
    obtain ⟨hr0, hrD⟩ := W.mem_feas_iff.mp hrf
    refine ⟨hr0, hrD, fun ν hν hνq => ?_⟩
    have hv : qb - ν ∈ W.feas qb := by
      refine W.mem_feas_iff.mpr ⟨fun i => ?_, ?_⟩
      · have h := hνq i
        show (0:ℝ) ≤ qb i - ν i
        linarith
      · have h : qb - (qb - ν) = ν := by abel
        rwa [h]
    have h := hopt _ hv
    rw [W.robj_eq_aobj_add, W.robj_eq_aobj_add] at h
    have h2 : qb - (qb - ν) = ν := by abel
    rw [h2] at h
    linarith [h]
  · rintro ⟨hr0, hrD, hopt⟩
    have hrf : r ∈ W.feas qb := W.mem_feas_iff.mpr ⟨hr0, hrD⟩
    refine ⟨hrf, fun v hv => ?_⟩
    obtain ⟨hv0, hvD⟩ := W.mem_feas_iff.mp hv
    rw [W.robj_eq_aobj_add, W.robj_eq_aobj_add]
    have h3 : W.aobj p (qb - r) ≤ W.aobj p (qb - v) := by
      refine hopt _ hvD fun i => ?_
      have h : (0:ℝ) ≤ v i := hv0 i
      show qb i - v i ≤ qb i
      linarith
    linarith [h3]

/-- The acceptance objective is lower semicontinuous on the effective domain. -/
theorem lowerSemicontinuousOn_aobj (p : ι → ℝ) :
    LowerSemicontinuousOn (W.aobj p) W.D := by
  have hdotc : Continuous fun v : ι → ℝ => p ⬝ᵥ v := by
    simp only [dotProduct]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)
  have hneg : Continuous fun v : ι → ℝ => -(p ⬝ᵥ v) := continuous_neg.comp hdotc
  simpa only [aobj, sub_eq_add_neg] using
    W.hcost_lsc.add hneg.continuousOn.lowerSemicontinuousOn

/-- A one-sided sequential consequence of lower semicontinuity. -/
theorem aobj_le_of_tendsto_of_eventually_le (p : ι → ℝ)
    {μs : ℕ → ι → ℝ} {μ : ι → ℝ} {b : ℝ}
    (hmem : ∀ k, μs k ∈ W.D) (hlim : Tendsto μs atTop (𝓝 μ))
    (hle : ∀ᶠ k in atTop, W.aobj p (μs k) ≤ b) :
    W.aobj p μ ≤ b := by
  have hcpt := (W.lowerSemicontinuousOn_aobj p).isCompact_inter_preimage_Iic
    W.hD_compact b
  have hseq : ∀ᶠ k in atTop, μs k ∈ W.D ∩ (W.aobj p) ⁻¹' Iic b :=
    (Eventually.of_forall hmem).and hle
  exact (hcpt.isClosed.mem_of_tendsto hlim hseq).2

/-- Convexity bounds the acceptance objective on a radial segment from zero. -/
theorem aobj_smul_le (hcost_conv : ConvexOn ℝ W.D W.cost) (p : ι → ℝ)
    {ν : ι → ℝ} (hν : ν ∈ W.D) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    W.aobj p (θ • ν) ≤ θ * W.aobj p ν + (1 - θ) * W.aobj p 0 := by
  have hc := hcost_conv.2 hν W.hD_zero hθ0 (sub_nonneg.mpr hθ1) (by ring)
  rw [smul_zero, add_zero] at hc
  unfold aobj
  rw [dotProduct_smul]
  simp only [smul_eq_mul, dotProduct_zero] at hc ⊢
  linarith

/-- **Closed graph along monotone capacities.** If capacities `qk k`
decrease to `q` (in the sense `q ≤ qk k` with convergence) and `rk k` are
optimal rejections converging to `r`, then `r` is an optimal rejection at
`q`.  Feasibility in the limit implies feasibility at every round, so no
lower hemicontinuity is needed. -/
theorem rejectSet_limit_antitone (p : ι → ℝ) {qk rk : ℕ → ι → ℝ}
    {q r : ι → ℝ} (hq0 : 0 ≤ q) (hqge : ∀ k, q ≤ qk k)
    (hqlim : Tendsto qk atTop (𝓝 q)) (hrlim : Tendsto rk atTop (𝓝 r))
    (hrk : ∀ k, rk k ∈ W.rejectSet p (qk k)) :
    r ∈ W.rejectSet p q := by
  have hqk0 : ∀ k, 0 ≤ qk k := fun k => le_trans hq0 (hqge k)
  have hchar : ∀ k, 0 ≤ rk k ∧ qk k - rk k ∈ W.D ∧
      ∀ ν ∈ W.D, ν ≤ qk k → W.aobj p (qk k - rk k) ≤ W.aobj p ν :=
    fun k => (W.mem_rejectSet_iff_acceptance (hqk0 k)).mp (hrk k)
  have hμlim : Tendsto (fun k => qk k - rk k) atTop (𝓝 (q - r)) :=
    hqlim.sub hrlim
  have hμD : q - r ∈ W.D :=
    W.hD_compact.isClosed.mem_of_tendsto hμlim
      (Eventually.of_forall fun k => (hchar k).2.1)
  refine (W.mem_rejectSet_iff_acceptance hq0).mpr ⟨?_, hμD, ?_⟩
  · have : IsClosed {v : ι → ℝ | 0 ≤ v} := isClosed_Ici (a := (0 : ι → ℝ))
    exact this.mem_of_tendsto hrlim (Eventually.of_forall fun k => (hchar k).1)
  · intro ν hν hνq
    have hstep : ∀ k, W.aobj p (qk k - rk k) ≤ W.aobj p ν :=
      fun k => (hchar k).2.2 ν hν (le_trans hνq (hqge k))
    exact W.aobj_le_of_tendsto_of_eventually_le p
      (fun k => (hchar k).2.1) hμlim (Eventually.of_forall hstep)

/-- Closed graph of optimal rejections for arbitrary convergent nonnegative
capacities. The proof rescales each limiting feasible acceptance toward zero
to obtain an eventually feasible comparison at every nearby capacity. -/
theorem rejectSet_limit (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost)
    (hDpos : ∀ μ ∈ W.D, 0 ≤ μ) (p : ι → ℝ)
    {qk rk : ℕ → ι → ℝ} {q r : ι → ℝ}
    (hqk0 : ∀ k, 0 ≤ qk k) (hq0 : 0 ≤ q)
    (hqlim : Tendsto qk atTop (𝓝 q)) (hrlim : Tendsto rk atTop (𝓝 r))
    (hrk : ∀ k, rk k ∈ W.rejectSet p (qk k)) :
    r ∈ W.rejectSet p q := by
  have hchar : ∀ k, 0 ≤ rk k ∧ qk k - rk k ∈ W.D ∧
      ∀ ν ∈ W.D, ν ≤ qk k →
        W.aobj p (qk k - rk k) ≤ W.aobj p ν :=
    fun k => (W.mem_rejectSet_iff_acceptance (hqk0 k)).mp (hrk k)
  have hμlim : Tendsto (fun k => qk k - rk k) atTop (𝓝 (q - r)) :=
    hqlim.sub hrlim
  have hμD : q - r ∈ W.D :=
    W.hD_compact.isClosed.mem_of_tendsto hμlim
      (Eventually.of_forall fun k => (hchar k).2.1)
  have hr0 : 0 ≤ r := by
    have hclosed : IsClosed {v : ι → ℝ | 0 ≤ v} :=
      isClosed_Ici (a := (0 : ι → ℝ))
    exact hclosed.mem_of_tendsto hrlim
      (Eventually.of_forall fun k => (hchar k).1)
  refine (W.mem_rejectSet_iff_acceptance hq0).mpr ⟨hr0, hμD, ?_⟩
  intro ν hν hνq
  have hν0 : 0 ≤ ν := hDpos ν hν
  have hθstep : ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
      W.aobj p (q - r) ≤ W.aobj p (θ • ν) := by
    intro θ hθ0 hθ1
    have hθν : θ • ν ∈ W.D := by
      have h : θ • ν + (1 - θ) • (0 : ι → ℝ) ∈ W.D :=
        hDconv hν W.hD_zero hθ0 (by linarith) (by ring)
      rwa [smul_zero, add_zero] at h
    have hev : ∀ᶠ k in atTop, θ • ν ≤ qk k := by
      have hall : ∀ᶠ k in atTop, ∀ i, (θ • ν) i ≤ qk k i := by
        rw [eventually_all]
        intro i
        rcases eq_or_lt_of_le (hq0 i) with hzero | hpos
        · have hνi : ν i = 0 := by
            have h1 := hνq i
            have h2 := hν0 i
            have h3 : (0 : ℝ) = q i := hzero
            linarith
          exact Eventually.of_forall fun k => by
            show θ * ν i ≤ qk k i
            rw [hνi, mul_zero]
            exact hqk0 k i
        · have hlt : (θ • ν) i < q i := by
            have h1 : θ * ν i ≤ θ * q i :=
              mul_le_mul_of_nonneg_left (hνq i) hθ0
            have h2 : θ * q i < q i := mul_lt_of_lt_one_left hpos hθ1
            show θ * ν i < q i
            linarith
          have hti : Tendsto (fun k => qk k i) atTop (𝓝 (q i)) :=
            tendsto_pi_nhds.mp hqlim i
          exact (hti.eventually (eventually_gt_nhds hlt)).mono
            fun k hk => le_of_lt hk
      exact hall.mono fun k hk i => hk i
    have hstep : ∀ᶠ k in atTop,
        W.aobj p (qk k - rk k) ≤ W.aobj p (θ • ν) := by
      exact hev.mono fun k hk => (hchar k).2.2 (θ • ν) hθν hk
    exact W.aobj_le_of_tendsto_of_eventually_le p
      (fun k => (hchar k).2.1) hμlim hstep
  have hs : ∀ m : ℕ,
      W.aobj p (q - r) ≤
        W.aobj p ((1 - 1 / (m + 1 : ℝ)) • ν) := by
    intro m
    have h1 : (0 : ℝ) < 1 / (m + 1 : ℝ) := by positivity
    have h2 : 1 / (m + 1 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact hθstep _ (by linarith) (by linarith)
  have hθtend : Tendsto (fun m : ℕ => 1 - 1 / (m + 1 : ℝ))
      atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => 1 / (m + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun m : ℕ => 1 - 1 / (m + 1 : ℝ))
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h
    simpa using h2
  have hrhs : Tendsto (fun m : ℕ =>
      (1 - 1 / (m + 1 : ℝ)) * W.aobj p ν +
        (1 - (1 - 1 / (m + 1 : ℝ))) * W.aobj p 0)
      atTop (𝓝 (W.aobj p ν)) := by
    simpa using (hθtend.mul_const (W.aobj p ν)).add
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        hθtend).mul_const (W.aobj p 0))
  refine ge_of_tendsto hrhs (Eventually.of_forall fun m => (hs m).trans ?_)
  have h1 : (0 : ℝ) < 1 / (m + 1 : ℝ) := by positivity
  have h2 : 1 / (m + 1 : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact W.aobj_smul_le hcost_conv p hν (by linarith) (by linarith)

/-- **The limit is a disposal fixed point.** If at each round `Pk k - Tk k`
is an optimal rejection at capacity `Pk k`, and proposals and acceptances
converge to a common limit `μ`, then `0` is an optimal rejection at capacity
`μ`: nothing is rejected at the limit.  Feasibility along the sequence is
recovered by scaling (`θ • ν`, `θ ↑ 1`), which needs `D` convex (with
`0 ∈ D` and `D` in the nonnegative orthant, both already available). -/
theorem rejectSet_fixedPoint_of_tendsto (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost)
    (hDpos : ∀ μ ∈ W.D, 0 ≤ μ) (γ : ι → ℝ) {Pk Tk : ℕ → ι → ℝ} {μ : ι → ℝ}
    (hP0 : ∀ k, 0 ≤ Pk k)
    (hrej : ∀ k, Pk k - Tk k ∈ W.rejectSet γ (Pk k))
    (hPlim : Tendsto Pk atTop (𝓝 μ)) (hTlim : Tendsto Tk atTop (𝓝 μ)) :
    0 ∈ W.rejectSet γ μ := by
  have hchar : ∀ k, 0 ≤ Pk k - Tk k ∧ Pk k - (Pk k - Tk k) ∈ W.D ∧
      ∀ ν ∈ W.D, ν ≤ Pk k →
        W.aobj γ (Pk k - (Pk k - Tk k)) ≤ W.aobj γ ν :=
    fun k => (W.mem_rejectSet_iff_acceptance (hP0 k)).mp (hrej k)
  have hTD : ∀ k, Tk k ∈ W.D := fun k => by
    have h := (hchar k).2.1
    have heq : Pk k - (Pk k - Tk k) = Tk k := by abel
    rwa [heq] at h
  have hμD : μ ∈ W.D :=
    W.hD_compact.isClosed.mem_of_tendsto hTlim (Eventually.of_forall hTD)
  have hμ0 : 0 ≤ μ := hDpos μ hμD
  refine (W.mem_rejectSet_iff_acceptance hμ0).mpr
    ⟨le_refl 0, by rwa [sub_zero], ?_⟩
  intro ν hν hνμ
  rw [sub_zero]
  have hν0 : 0 ≤ ν := hDpos ν hν
  -- Step 1: for every scale θ ∈ [0,1), the limit beats θ • ν.
  have hθstep : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → W.aobj γ μ ≤ W.aobj γ (θ • ν) := by
    intro θ hθ0 hθ1
    have hθν : θ • ν ∈ W.D := by
      have h : θ • ν + (1 - θ) • (0 : ι → ℝ) ∈ W.D :=
        hDconv hν W.hD_zero hθ0 (by linarith) (by ring)
      rwa [smul_zero, add_zero] at h
    -- θ • ν is eventually feasible at capacity Pk k.
    have hev : ∀ᶠ k in atTop, θ • ν ≤ Pk k := by
      have hall : ∀ᶠ k in atTop, ∀ i, (θ • ν) i ≤ Pk k i := by
        rw [eventually_all]
        intro i
        rcases eq_or_lt_of_le (hμ0 i) with h0 | hpos
        · have hνi : ν i = 0 := by
            have h1 := hνμ i
            have h2 := hν0 i
            have h3 : (0:ℝ) = μ i := h0
            linarith
          refine Eventually.of_forall fun k => ?_
          have h4 := hP0 k i
          show θ * ν i ≤ Pk k i
          rw [hνi, mul_zero]
          exact h4
        · have hlt : (θ • ν) i < μ i := by
            have h1 : θ * ν i ≤ θ * μ i :=
              mul_le_mul_of_nonneg_left (hνμ i) hθ0
            have h2 : θ * μ i < μ i := mul_lt_of_lt_one_left hpos hθ1
            show θ * ν i < μ i
            linarith
          have hti : Tendsto (fun k => Pk k i) atTop (𝓝 (μ i)) :=
            tendsto_pi_nhds.mp hPlim i
          exact (hti.eventually (eventually_gt_nhds hlt)).mono
            fun k hk => le_of_lt hk
      exact hall.mono fun k hk i => hk i
    have hstep : ∀ᶠ k in atTop, W.aobj γ (Tk k) ≤ W.aobj γ (θ • ν) := by
      refine hev.mono fun k hk => ?_
      have h := (hchar k).2.2 (θ • ν) hθν hk
      have heq : Pk k - (Pk k - Tk k) = Tk k := by abel
      rwa [heq] at h
    exact W.aobj_le_of_tendsto_of_eventually_le γ hTD hTlim hstep
  -- Step 2: let θ ↑ 1 along the sequence 1 - 1/(m+1).
  have hs : ∀ m : ℕ, W.aobj γ μ ≤ W.aobj γ ((1 - 1 / (m + 1 : ℝ)) • ν) := by
    intro m
    have h1 : (0:ℝ) < 1 / (m + 1 : ℝ) := by positivity
    have h2 : 1 / (m + 1 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact hθstep _ (by linarith) (by linarith)
  have hθtend : Tendsto (fun m : ℕ => 1 - 1 / (m + 1 : ℝ)) atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => 1 / (m + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun m : ℕ => 1 - 1 / (m + 1 : ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h
    simpa using h2
  have hrhs : Tendsto (fun m : ℕ =>
      (1 - 1 / (m + 1 : ℝ)) * W.aobj γ ν +
        (1 - (1 - 1 / (m + 1 : ℝ))) * W.aobj γ 0)
      atTop (𝓝 (W.aobj γ ν)) := by
    simpa using (hθtend.mul_const (W.aobj γ ν)).add
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        hθtend).mul_const (W.aobj γ 0))
  refine ge_of_tendsto hrhs (Eventually.of_forall fun m => (hs m).trans ?_)
  have h1 : (0 : ℝ) < 1 / (m + 1 : ℝ) := by positivity
  have h2 : 1 / (m + 1 : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact W.aobj_smul_le hcost_conv γ hν (by linarith) (by linarith)

end WelfareDual

/-! ## Theorem 3, limit identification -/

variable {ι : Type*} [Fintype ι] {WG WH : WelfareDual ι} {α γ : ι → ℝ}

/-- **GHS Theorem 3, τ-free form (limit identification).** Run Algorithm 1
from a nonnegative initial availability.  Then availabilities decrease to
`Ainf`, and along a subsequence the proposals and tentative acceptances
converge to a common limit `μ` with

* `Ainf - μ ∈ rejectSet_G α Ainf` — the accepted mass `μ` is proposer-optimal
  at the limiting availability (`μ ∈ M^G(α, Ainf)`);
* `0 ∈ rejectSet_H γ μ` — nothing is rejected at `μ`: the limit is a fixed
  point of the disposal phase (`μ ∈ M^H(γ, μ)`).

The further decomposition into waiting times (the KKT multipliers of the
paper's statement) is not taken here. -/
theorem theorem3_limit (hcG : Exchangeable WG.cFn)
    (hDG : ∀ μ ∈ WG.D, 0 ≤ μ) (hDH : ∀ μ ∈ WH.D, 0 ≤ μ)
    (hDHconv : Convex ℝ WH.D) (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) :
    ∃ (s : DASequences ι) (μ : ι → ℝ) (φ : ℕ → ℕ), s.A 0 = A0 ∧
      StrictMono φ ∧
      Tendsto (fun k => s.P (φ k)) atTop (𝓝 μ) ∧
      Tendsto (fun k => s.T (φ k)) atTop (𝓝 μ) ∧
      0 ≤ μ ∧ μ ≤ s.Ainf ∧
      s.Ainf - μ ∈ WG.rejectSet α s.Ainf ∧
      0 ∈ WH.rejectSet γ μ := by
  obtain ⟨s, hs0, hG, hH, -⟩ :=
    algorithm_wellDefined (WG := WG) (WH := WH) (α := α) (γ := γ)
      hcG hDG hDH hA0
  obtain ⟨μ, hμbox, φ, hφ, hPtend, hTtend⟩ := s.exists_subseq_tendsto
  have hAtend : Tendsto (fun k => s.A (φ k)) atTop (𝓝 s.Ainf) :=
    s.tendsto_A.comp hφ.tendsto_atTop
  have hμA : μ ≤ s.Ainf := by
    intro i
    refine le_of_tendsto_of_tendsto' (tendsto_pi_nhds.mp hPtend i)
      (tendsto_pi_nhds.mp hAtend i) fun k => ?_
    exact s.P_le_A (φ k) i
  refine ⟨s, μ, φ, hs0, hφ, hPtend, hTtend, hμbox.1, hμA, ?_, ?_⟩
  · refine WG.rejectSet_limit_antitone α s.nonneg_Ainf
      (fun k => s.Ainf_le (φ k)) hAtend (hAtend.sub hPtend) ?_
    exact fun k => hG (φ k)
  · refine WH.rejectSet_fixedPoint_of_tendsto hDHconv hHcost_conv hDH γ
      (fun k => le_trans (s.nonneg_T (φ k)) (s.T_le_P (φ k)))
      (fun k => hH (φ k)) hPtend hTtend

end GHS
