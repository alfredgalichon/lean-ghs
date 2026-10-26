import GHS.CapacityMCS
import Mathlib.Topology.Semicontinuous

/-!
# GHS Phase 6: welfare data and Lemma 1 (attainment of the rejected sets)

The approved design for the algorithm side: the dual welfare function
`c = G*` is carried as a bundle `WelfareDual` — a compact set `D` of feasible
acceptances containing `0`, with a lower-semicontinuous real-valued cost on
`D`, extended by `⊤` off `D`.

Machine-checked here, for capacities `qb ≥ 0`:

* `rejectSet_nonempty` — **Lemma 1**: the rejected set
  `r(p, qb) = argmin_{u ≥ 0} { c(qb - u) + ⟨p, u⟩ }` is nonempty;
* `rejectSet_isClosed`, `obj_finite_somewhere` — the side conditions of
  `qOrderSet_capacity` and Proposition 2;
* `exists_rejection_le` — the fully discharged Proposition 3 engine: for
  exchangeable `c` and `0 ≤ qb ≤ qb'`, every rejection at capacity `qb'`
  dominates a rejection at capacity `qb`, with no side conditions.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set

namespace GHS

/-- Dual welfare data: a compact feasible set of acceptances containing `0`,
with a lower-semicontinuous real cost on it. -/
structure WelfareDual (ι : Type*) [Fintype ι] where
  /-- the domain of the dual welfare function (`dom G*`) -/
  D : Set (ι → ℝ)
  /-- the (finite) cost on the domain -/
  cost : (ι → ℝ) → ℝ
  hD_compact : IsCompact D
  hD_zero : 0 ∈ D
  hcost_lsc : LowerSemicontinuousOn cost D

namespace WelfareDual

variable {ι : Type*} [Fintype ι] (W : WelfareDual ι)

open Classical in
/-- The extended-real dual welfare function `c = cost + ι_D`. -/
noncomputable def cFn : (ι → ℝ) → ERealTop :=
  fun μ => if μ ∈ W.D then ((W.cost μ : ℝ) : ERealTop) else ⊤

/-- The capacity objective `u ↦ c(qb - u) + ⟨p, u⟩`. -/
noncomputable def obj (p qb : ι → ℝ) : (ι → ℝ) → ERealTop :=
  fun u => W.cFn (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop)

/-- The rejected set `r(p, qb)`. -/
noncomputable def rejectSet (p qb : ι → ℝ) : Set (ι → ℝ) :=
  argminOn (W.obj p qb) {v : ι → ℝ | 0 ≤ v}

/-- The effective feasible set: nonnegative `u` with `qb - u ∈ D`. -/
def feas (qb : ι → ℝ) : Set (ι → ℝ) :=
  {v : ι → ℝ | 0 ≤ v} ∩ ((fun μ => qb - μ) '' W.D)

/-- The real-valued objective. -/
def robj (p qb : ι → ℝ) : (ι → ℝ) → ℝ :=
  fun u => W.cost (qb - u) + p ⬝ᵥ u

theorem feas_compact (qb : ι → ℝ) : IsCompact (W.feas qb) := by
  refine IsCompact.inter_left ?_ ?_
  · exact W.hD_compact.image (continuous_const.sub continuous_id)
  · show IsClosed (Ici (0 : ι → ℝ))
    exact isClosed_Ici

theorem mem_D_of_mem_feas {qb u : ι → ℝ} (hu : u ∈ W.feas qb) :
    qb - u ∈ W.D := by
  obtain ⟨-, μ, hμ, rfl⟩ := hu
  have h : qb - (qb - μ) = μ := by abel
  rw [h]
  exact hμ

theorem robj_lowerSemicontinuousOn (p qb : ι → ℝ) :
    LowerSemicontinuousOn (W.robj p qb) (W.feas qb) := by
  refine LowerSemicontinuousOn.add ?_ ?_
  · have hg : ContinuousOn (fun u : ι → ℝ => qb - u) (W.feas qb) :=
      (continuous_const.sub continuous_id).continuousOn
    have hm : MapsTo (fun u : ι → ℝ => qb - u) (W.feas qb) W.D :=
      fun u hu => W.mem_D_of_mem_feas hu
    have hcomp := W.hcost_lsc.comp hg hm
    simpa only [Function.comp_apply] using hcomp
  · have h : Continuous (fun u : ι → ℝ => p ⬝ᵥ u) := by
      simp only [dotProduct]
      exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)
    exact h.continuousOn.lowerSemicontinuousOn

theorem cFn_of_mem {μ : ι → ℝ} (hμ : μ ∈ W.D) :
    W.cFn μ = ((W.cost μ : ℝ) : ERealTop) := if_pos hμ

theorem cFn_of_not_mem {μ : ι → ℝ} (hμ : μ ∉ W.D) : W.cFn μ = ⊤ := if_neg hμ

theorem obj_eq_of_mem_feas {p qb u : ι → ℝ} (hu : u ∈ W.feas qb) :
    W.obj p qb u = ((W.robj p qb u : ℝ) : ERealTop) := by
  rw [obj, W.cFn_of_mem (W.mem_D_of_mem_feas hu), ← WithTop.coe_add]
  rfl

theorem obj_eq_top {p qb u : ι → ℝ} (hu : qb - u ∉ W.D) :
    W.obj p qb u = ⊤ := by
  rw [obj, W.cFn_of_not_mem hu, top_add]

/-- The rejected set is the set of feasible minimizers of the real
objective. -/
theorem rejectSet_eq (p qb : ι → ℝ) (hqb : 0 ≤ qb) :
    ∃ u₀ ∈ W.feas qb,
      W.rejectSet p qb = {u ∈ W.feas qb | W.robj p qb u ≤ W.robj p qb u₀}
        ∧ IsMinOn (W.robj p qb) (W.feas qb) u₀ := by
  have hne : (W.feas qb).Nonempty := ⟨qb, hqb, 0, W.hD_zero, by abel⟩
  obtain ⟨u₀, hu₀, hmin⟩ :=
    (W.robj_lowerSemicontinuousOn p qb).exists_isMinOn hne (W.feas_compact qb)
  refine ⟨u₀, hu₀, ?_, hmin⟩
  ext u
  constructor
  · rintro ⟨humem, hule⟩
    have h1 := hule u₀ hu₀.1
    rw [W.obj_eq_of_mem_feas hu₀] at h1
    have h2 : W.obj p qb u ≠ ⊤ := ne_top_of_le_ne_top (WithTop.coe_ne_top) h1
    have h3 : qb - u ∈ W.D := by
      by_contra hcon
      exact h2 (W.obj_eq_top hcon)
    have h4 : u ∈ W.feas qb := ⟨humem, qb - u, h3, by abel⟩
    refine ⟨h4, ?_⟩
    rw [W.obj_eq_of_mem_feas h4] at h1
    exact_mod_cast h1
  · rintro ⟨humem, hle⟩
    refine ⟨humem.1, fun w hw => ?_⟩
    rw [W.obj_eq_of_mem_feas humem]
    by_cases hwD : qb - w ∈ W.D
    · have hwfeas : w ∈ W.feas qb := ⟨hw, qb - w, hwD, by abel⟩
      rw [W.obj_eq_of_mem_feas hwfeas]
      have h5 := hmin hwfeas
      refine WithTop.coe_le_coe.mpr ?_
      exact le_trans hle h5
    · rw [W.obj_eq_top hwD]
      exact le_top

/-- **Lemma 1**: the rejected set is nonempty. -/
theorem rejectSet_nonempty (p : ι → ℝ) {qb : ι → ℝ} (hqb : 0 ≤ qb) :
    (W.rejectSet p qb).Nonempty := by
  obtain ⟨u₀, hu₀, heq, hmin⟩ := W.rejectSet_eq p qb hqb
  exact ⟨u₀, heq ▸ ⟨hu₀, le_refl _⟩⟩

/-- The rejected set is closed. -/
theorem rejectSet_isClosed (p : ι → ℝ) {qb : ι → ℝ} (hqb : 0 ≤ qb) :
    IsClosed (W.rejectSet p qb) := by
  obtain ⟨u₀, hu₀, heq, hmin⟩ := W.rejectSet_eq p qb hqb
  rw [heq]
  have h1 : {u ∈ W.feas qb | W.robj p qb u ≤ W.robj p qb u₀}
      = W.feas qb ∩ (W.robj p qb) ⁻¹' (Iic (W.robj p qb u₀)) := rfl
  rw [h1]
  exact ((W.robj_lowerSemicontinuousOn p qb).isCompact_inter_preimage_Iic
    (W.feas_compact qb) (W.robj p qb u₀)).isClosed

/-- The objective is finite somewhere on `{u ≥ 0}` (the properness side
condition of `qOrderSet_capacity`). -/
theorem obj_finite_somewhere (p : ι → ℝ) {qb : ι → ℝ} (hqb : 0 ≤ qb) :
    ∃ u ∈ {v : ι → ℝ | 0 ≤ v}, W.cFn (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤ := by
  refine ⟨qb, hqb, ?_⟩
  have hfeas : qb ∈ W.feas qb := ⟨hqb, 0, W.hD_zero, by abel⟩
  have h := W.obj_eq_of_mem_feas (p := p) hfeas
  rw [obj] at h
  rw [h]
  exact WithTop.coe_ne_top

/-- **The Proposition 3 engine, fully discharged**: for exchangeable `c` and
capacities `0 ≤ qb ≤ qb'`, every rejection at the larger capacity dominates a
rejection at the smaller one. -/
theorem exists_rejection_le (hc : Exchangeable W.cFn) (p : ι → ℝ)
    {qb qb' : ι → ℝ} (hqb : 0 ≤ qb) (hq : qb ≤ qb') :
    ∀ r' ∈ W.rejectSet p qb', ∃ r ∈ W.rejectSet p qb, r ≤ r' := by
  have hqb' : 0 ≤ qb' := le_trans hqb hq
  exact exists_rejection_le_of_capacity_le hc p hq
    (W.obj_finite_somewhere p hqb) (W.obj_finite_somewhere p hqb')
    (W.rejectSet_isClosed p hqb) (W.rejectSet_isClosed p hqb')
    (W.rejectSet_nonempty p hqb) (W.rejectSet_nonempty p hqb')

/-! ## The Proposition 3 induction steps -/

/-- **Proposal-phase step (Proposition 3).** Given a state with invariants
`0 ≤ T ≤ P ≤ A` where `A - P` is a current rejection, the next capacity
`A' = A - (P - T)` admits a proposal `P'` that dominates the old tentative
acceptance `T` — so the box-constrained proposal phase of Algorithm 1
coincides with the capacity-constrained one. -/
theorem exists_proposal_ge (hc : Exchangeable W.cFn) (α : ι → ℝ)
    {A P T : ι → ℝ} (hT0 : 0 ≤ T) (hTP : T ≤ P) (hPA : P ≤ A)
    (hA'0 : 0 ≤ A - (P - T)) (hrej : A - P ∈ W.rejectSet α A) :
    ∃ P', T ≤ P' ∧ (A - (P - T)) - P' ∈ W.rejectSet α (A - (P - T)) := by
  have hle : A - (P - T) ≤ A := by
    intro i
    have h1 : (0:ℝ) ≤ T i := hT0 i
    have h2 : T i ≤ P i := hTP i
    show A i - (P i - T i) ≤ A i
    linarith
  obtain ⟨r', hr'mem, hr'le⟩ :=
    W.exists_rejection_le hc α hA'0 hle (A - P) hrej
  refine ⟨(A - (P - T)) - r', ?_, ?_⟩
  · intro i
    have h1 : r' i ≤ A i - P i := hr'le i
    have h2 : T i ≤ P i := hTP i
    show T i ≤ (A i - (P i - T i)) - r' i
    linarith
  · have h : (A - (P - T)) - ((A - (P - T)) - r') = r' := by abel
    rwa [h]

/-- **Disposal-phase step (Proposition 3).** For a nonnegative proposal `P'`
(and acceptances constrained to be nonnegative, `D ⊆ {μ ≥ 0}` as in the
paper), the disposal phase produces `0 ≤ T' ≤ P'` with `P' - T'` a
rejection. -/
theorem exists_disposal (hDpos : ∀ μ ∈ W.D, 0 ≤ μ) (γ : ι → ℝ)
    {P' : ι → ℝ} (hP' : 0 ≤ P') :
    ∃ T', 0 ≤ T' ∧ T' ≤ P' ∧ P' - T' ∈ W.rejectSet γ P' := by
  obtain ⟨u₀, hu₀, heq, hmin⟩ := W.rejectSet_eq γ P' hP'
  obtain ⟨r, hr⟩ := W.rejectSet_nonempty γ (qb := P') hP'
  have hrfeas : r ∈ W.feas P' := by
    rw [heq] at hr
    exact hr.1
  refine ⟨P' - r, ?_, ?_, ?_⟩
  · intro i
    have h1 := hDpos _ (W.mem_D_of_mem_feas hrfeas) i
    show (0:ℝ) ≤ P' i - r i
    exact h1
  · intro i
    have h1 : (0:ℝ) ≤ r i := hrfeas.1 i
    show P' i - r i ≤ P' i
    linarith
  · have h : P' - (P' - r) = r := by abel
    rwa [h]

end WelfareDual

end GHS
