import GHS.Orders
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# GHS Phase 6, item 26: random-utility welfare is submodular

The paper's leading example of a welfare function: the expected maximum
`G(U) = E[max_y (U_y + ε_y)]` of coordinate payoffs plus random shocks, the
maximum including an outside option with payoff `0 + ε_0`. Machine-checked
here first for finite-support shocks, then for an arbitrary finite measure and
integrable coordinate shocks:

* `sup'_submodular`: the core lattice fact, sharper than needed. A finite
  maximum of alternatives whose payoffs split lattice operations
  (`f j (u ⊔ v) = max (f j u) (f j v)` and dually) is submodular.  Coordinate
  evaluations `u ↦ u i` and constants split, hence so does any
  coordinate-plus-intercept family.
* `emax`, `submodular_emax`: `G(U) = Σ_ω π_ω max_{y ∈ ι ∪ {0}} (U_y + ε_y(ω))`
  is submodular (in the paper's vocabulary `GHS.Submodular`, values embedded
  in `ℝ ∪ {+∞}`) for any nonnegative weights; no normalization is needed.
* `randomUtilityWelfare`, `submodular_randomUtilityWelfare`: the same result
  for the Bochner integral with respect to any finite measure. Integrability of
  every shock coordinate implies integrability of the finite maximum.

Mathlib-only (part of the standalone `GHS` target).
-/

namespace GHS

variable {ι : Type*}

/-- **Submodularity of a finite maximum.** If every alternative's payoff
splits the lattice operations of `ℝ^ι` into `max`/`min`, as coordinate
evaluations plus intercepts do, then the pointwise maximum over a finite
nonempty family is submodular. -/
theorem sup'_submodular {J : Type*} (s : Finset J) (hs : s.Nonempty)
    (f : J → (ι → ℝ) → ℝ)
    (hsup : ∀ j ∈ s, ∀ u v : ι → ℝ, f j (u ⊔ v) = max (f j u) (f j v))
    (hinf : ∀ j ∈ s, ∀ u v : ι → ℝ, f j (u ⊓ v) = min (f j u) (f j v))
    (u v : ι → ℝ) :
    (s.sup' hs fun j => f j (u ⊓ v)) + (s.sup' hs fun j => f j (u ⊔ v))
      ≤ (s.sup' hs fun j => f j u) + (s.sup' hs fun j => f j v) := by
  obtain ⟨y, hy, hyeq⟩ := Finset.exists_mem_eq_sup' hs (fun j => f j (u ⊔ v))
  obtain ⟨z, hz, hzeq⟩ := Finset.exists_mem_eq_sup' hs (fun j => f j (u ⊓ v))
  rw [hyeq, hzeq, hsup y hy, hinf z hz]
  rcases le_total (f y u) (f y v) with h | h
  · have h1 : max (f y u) (f y v) = f y v := max_eq_right h
    have h2 : min (f z u) (f z v) ≤ f z u := min_le_left _ _
    have h3 : f y v ≤ s.sup' hs fun j => f j v :=
      Finset.le_sup' (fun j => f j v) hy
    have h4 : f z u ≤ s.sup' hs fun j => f j u :=
      Finset.le_sup' (fun j => f j u) hz
    rw [h1]
    linarith
  · have h1 : max (f y u) (f y v) = f y u := max_eq_left h
    have h2 : min (f z u) (f z v) ≤ f z v := min_le_right _ _
    have h3 : f y u ≤ s.sup' hs fun j => f j u :=
      Finset.le_sup' (fun j => f j u) hy
    have h4 : f z v ≤ s.sup' hs fun j => f j v :=
      Finset.le_sup' (fun j => f j v) hz
    rw [h1]
    linarith

variable [Fintype ι] {Ω : Type*} [Fintype Ω]

/-- Finite-support random-utility welfare: the weighted expected maximum of
coordinate payoffs plus shocks, over the alternatives `ι` extended by the
outside option (`none`, systematic payoff `0`). -/
noncomputable def emax (π : Ω → ℝ) (ε : Ω → Option ι → ℝ) : (ι → ℝ) → ℝ :=
  fun u => ∑ ω, π ω *
    (Finset.univ.sup' Finset.univ_nonempty fun y : Option ι =>
      y.elim 0 u + ε ω y)

/-- **Item 26 (finite support): the random-utility welfare is submodular.**
For any nonnegative weights `π` and any shock realizations `ε`,
`G(U) = Σ_ω π_ω · max_{y ∈ ι ∪ {0}} (U_y + ε_y(ω))` is submodular. -/
theorem submodular_emax (π : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω)
    (ε : Ω → Option ι → ℝ) :
    Submodular (fun u => ((emax π ε u : ℝ) : ERealTop)) := by
  intro p p'
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  have key : ∀ ω : Ω,
      (Finset.univ.sup' Finset.univ_nonempty fun y : Option ι =>
        y.elim 0 (p ⊓ p') + ε ω y)
      + (Finset.univ.sup' Finset.univ_nonempty fun y : Option ι =>
        y.elim 0 (p ⊔ p') + ε ω y)
      ≤ (Finset.univ.sup' Finset.univ_nonempty fun y : Option ι =>
          y.elim 0 p + ε ω y)
        + (Finset.univ.sup' Finset.univ_nonempty fun y : Option ι =>
          y.elim 0 p' + ε ω y) := by
    intro ω
    refine sup'_submodular Finset.univ Finset.univ_nonempty
      (fun y u => y.elim 0 u + ε ω y) ?_ ?_ p p'
    · intro y _ u v
      cases y with
      | none =>
        show (0:ℝ) + ε ω none = max ((0:ℝ) + ε ω none) ((0:ℝ) + ε ω none)
        rw [max_self]
      | some i =>
        show max (u i) (v i) + ε ω (some i)
          = max (u i + ε ω (some i)) (v i + ε ω (some i))
        rw [max_add_add_right]
    · intro y _ u v
      cases y with
      | none =>
        show (0:ℝ) + ε ω none = min ((0:ℝ) + ε ω none) ((0:ℝ) + ε ω none)
        rw [min_self]
      | some i =>
        show min (u i) (v i) + ε ω (some i)
          = min (u i + ε ω (some i)) (v i + ε ω (some i))
        rw [min_add_add_right]
  show emax π ε (p ⊓ p') + emax π ε (p ⊔ p') ≤ emax π ε p + emax π ε p'
  unfold emax
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [← mul_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (key ω) (hπ ω)

section GeneralMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)

/-- The realized maximum in a random-utility model, including the outside
option `none`, whose systematic utility is zero. -/
noncomputable def randomUtilityMax (ε : Ω → Option ι → ℝ)
    (u : ι → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun y : Option ι =>
    y.elim 0 u + ε ω y

/-- A finite maximum of integrable real-valued functions is integrable. -/
theorem integrable_finset_sup' {J : Type*} (s : Finset J) (hs : s.Nonempty)
    (f : J → Ω → ℝ)
    (hf : ∀ j ∈ s, MeasureTheory.Integrable (f j) μ) :
    MeasureTheory.Integrable (fun ω => s.sup' hs fun j => f j ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · have ha_int : MeasureTheory.Integrable (f a) μ := hf a (Finset.mem_insert_self a s)
        have hs_int : MeasureTheory.Integrable (fun ω => s.sup' hs' fun j => f j ω) μ :=
          ih hs' fun j hj => hf j (Finset.mem_insert_of_mem hj)
        simpa only [Finset.sup'_insert hs'] using ha_int.sup hs_int
      · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        simpa using hf a (Finset.mem_singleton_self a)

/-- Integrable coordinate shocks make the realized finite random-utility
maximum integrable at every vector of systematic utilities. -/
theorem integrable_randomUtilityMax [MeasureTheory.IsFiniteMeasure μ]
    (ε : Ω → Option ι → ℝ)
    (hε : ∀ y, MeasureTheory.Integrable (fun ω => ε ω y) μ)
    (u : ι → ℝ) :
    MeasureTheory.Integrable (randomUtilityMax ε u) μ := by
  apply integrable_finset_sup' μ Finset.univ Finset.univ_nonempty
  intro y _
  exact (MeasureTheory.integrable_const (y.elim 0 u)).add (hε y)

/-- Expected random-utility welfare under an arbitrary finite measure. -/
noncomputable def randomUtilityWelfare
    (ε : Ω → Option ι → ℝ) (u : ι → ℝ) : ℝ :=
  ∫ ω, randomUtilityMax ε u ω ∂μ

omit [MeasurableSpace Ω] in
/-- The realized maximum is pointwise submodular in systematic utilities. -/
theorem randomUtilityMax_submodular
    (ε : Ω → Option ι → ℝ) (ω : Ω) (u v : ι → ℝ) :
    randomUtilityMax ε (u ⊓ v) ω + randomUtilityMax ε (u ⊔ v) ω
      ≤ randomUtilityMax ε u ω + randomUtilityMax ε v ω := by
  apply sup'_submodular Finset.univ Finset.univ_nonempty
      (fun y w => y.elim 0 w + ε ω y)
  · intro y _ w w'
    cases y with
    | none => simp
    | some i =>
      show max (w i) (w' i) + ε ω (some i)
        = max (w i + ε ω (some i)) (w' i + ε ω (some i))
      rw [max_add_add_right]
  · intro y _ w w'
    cases y with
    | none => simp
    | some i =>
      show min (w i) (w' i) + ε ω (some i)
        = min (w i + ε ω (some i)) (w' i + ε ω (some i))
      rw [min_add_add_right]

/-- **Random-utility welfare is submodular for general shock distributions.**
If every shock coordinate is integrable with respect to a finite measure, then
the expected maximum of the alternative-specific utilities is submodular. A
probability measure is a special case. -/
theorem submodular_randomUtilityWelfare
    [MeasureTheory.IsFiniteMeasure μ]
    (ε : Ω → Option ι → ℝ)
    (hε : ∀ y, MeasureTheory.Integrable (fun ω => ε ω y) μ) :
    Submodular (fun u => ((randomUtilityWelfare μ ε u : ℝ) : ERealTop)) := by
  intro u v
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  have huv_inf := integrable_randomUtilityMax μ ε hε (u ⊓ v)
  have huv_sup := integrable_randomUtilityMax μ ε hε (u ⊔ v)
  have hu := integrable_randomUtilityMax μ ε hε u
  have hv := integrable_randomUtilityMax μ ε hε v
  show randomUtilityWelfare μ ε (u ⊓ v) + randomUtilityWelfare μ ε (u ⊔ v)
      ≤ randomUtilityWelfare μ ε u + randomUtilityWelfare μ ε v
  unfold randomUtilityWelfare
  rw [← MeasureTheory.integral_add huv_inf huv_sup,
    ← MeasureTheory.integral_add hu hv]
  exact MeasureTheory.integral_mono (huv_inf.add huv_sup) (hu.add hv)
    fun ω => randomUtilityMax_submodular ε ω u v

end GeneralMeasure

end GHS
