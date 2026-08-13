import GHS.Orders
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# GHS Phase 6, item 26: random-utility welfare is submodular (finite support)

The paper's leading example of a welfare function: the expected maximum
`G(U) = E[max_y (U_y + ε_y)]` of coordinate payoffs plus random shocks, the
maximum including an outside option with payoff `0 + ε_0`.  Machine-checked
here for shocks with **finite support** (`Ω` a finite probability space):

* `sup'_submodular` — the core lattice fact, sharper than needed: a finite
  maximum of alternatives whose payoffs split lattice operations
  (`f j (u ⊔ v) = max (f j u) (f j v)` and dually) is submodular.  Coordinate
  evaluations `u ↦ u i` and constants split, hence so does any
  coordinate-plus-intercept family.
* `emax`, `submodular_emax` — `G(U) = Σ_ω π_ω max_{y ∈ ι ∪ {0}} (U_y + ε_y(ω))`
  is submodular (in the paper's vocabulary `GHS.Submodular`, values embedded
  in `ℝ ∪ {+∞}`) for any nonnegative weights — no normalization needed.

Mathlib-only (part of the standalone `GHS` target).
-/

namespace GHS

variable {ι : Type*}

/-- **Submodularity of a finite maximum.** If every alternative's payoff
splits the lattice operations of `ℝ^ι` into `max`/`min` — as coordinate
evaluations plus intercepts do — then the pointwise maximum over a finite
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

end GHS
