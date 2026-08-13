import GHS.WelfareData
import GHS.DeferredAcceptance

/-!
# GHS Phase 6: Proposition 3 — Algorithm 1 is well defined

The recursion assembling the deferred-acceptance sequences from the two step
lemmas of `GHS/WelfareData.lean`.  A `DAState` carries one round's
availabilities/proposals/acceptances together with the invariants
`0 ≤ T ≤ P ≤ A` and the two optimality certificates (`A - P` is a
proposer-side rejection at capacity `A`; `P - T` a disposer-side rejection at
capacity `P`).  `daStep` advances one round (choice from
`exists_proposal_ge` — whose output dominates the previous tentative
acceptance, so the box-constrained proposal phase of Algorithm 1 coincides
with the capacity-constrained one — and `exists_disposal`); `daInit` starts
from any nonnegative availability.

* `algorithm_wellDefined` — **Proposition 3**: for exchangeable proposer cost
  and both welfare domains in the nonnegative orthant, there exist sequences
  satisfying all of Algorithm 1's phases; packaged as a `DASequences`, so the
  convergence facts of `GHS/DeferredAcceptance.lean` (availabilities
  converge, rejected masses vanish) apply immediately.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set

namespace GHS

variable {ι : Type*} [Fintype ι]

/-- One round of Algorithm 1, with its invariants and optimality
certificates. -/
structure DAState (WG WH : WelfareDual ι) (α γ : ι → ℝ) where
  /-- available masses -/
  A : ι → ℝ
  /-- proposed masses -/
  P : ι → ℝ
  /-- tentatively accepted masses -/
  T : ι → ℝ
  hT0 : 0 ≤ T
  hTP : T ≤ P
  hPA : P ≤ A
  hrejG : A - P ∈ WG.rejectSet α A
  hrejH : P - T ∈ WH.rejectSet γ P

variable {WG WH : WelfareDual ι} {α γ : ι → ℝ}

/-- One step of Algorithm 1: shrink the availability by the rejected mass,
propose (dominating the old tentative acceptance), dispose. -/
noncomputable def daStep (hcG : Exchangeable WG.cFn)
    (hDH : ∀ μ ∈ WH.D, 0 ≤ μ) (s : DAState WG WH α γ) : DAState WG WH α γ :=
  have hA'0 : 0 ≤ s.A - (s.P - s.T) := fun i => by
    have h1 : s.P i ≤ s.A i := s.hPA i
    have h2 : (0:ℝ) ≤ s.T i := s.hT0 i
    show (0:ℝ) ≤ s.A i - (s.P i - s.T i)
    linarith
  have hP := WG.exists_proposal_ge hcG α s.hT0 s.hTP s.hPA hA'0 s.hrejG
  have hP'0 : 0 ≤ hP.choose := le_trans s.hT0 hP.choose_spec.1
  have hT := WH.exists_disposal hDH γ hP'0
  { A := s.A - (s.P - s.T)
    P := hP.choose
    T := hT.choose
    hT0 := hT.choose_spec.1
    hTP := hT.choose_spec.2.1
    hPA := fun i => by
      have h1 : (0:ℝ) ≤ (s.A - (s.P - s.T) - hP.choose) i := hP.choose_spec.2.1 i
      show hP.choose i ≤ (s.A - (s.P - s.T)) i
      have h2 : (s.A - (s.P - s.T) - hP.choose) i
          = (s.A - (s.P - s.T)) i - hP.choose i := rfl
      rw [h2] at h1
      linarith
    hrejG := hP.choose_spec.2
    hrejH := hT.choose_spec.2.2 }

/-- The next proposal dominates the previous tentative acceptance. -/
theorem daStep_cross (hcG : Exchangeable WG.cFn)
    (hDH : ∀ μ ∈ WH.D, 0 ≤ μ) (s : DAState WG WH α γ) :
    s.T ≤ (daStep hcG hDH s).P := by
  unfold daStep
  dsimp only
  exact (WG.exists_proposal_ge hcG α s.hT0 s.hTP s.hPA
    (by
      intro i
      have h1 := s.hPA i
      have h2 : (0 : ℝ) ≤ s.T i := s.hT0 i
      change (0 : ℝ) ≤ s.A i - (s.P i - s.T i)
      linarith)
    s.hrejG).choose_spec.1

/-- The initial round: propose at the initial availability, dispose. -/
noncomputable def daInit (hDG : ∀ μ ∈ WG.D, 0 ≤ μ) (hDH : ∀ μ ∈ WH.D, 0 ≤ μ)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) : DAState WG WH α γ :=
  have hP := WG.exists_disposal hDG α hA0
  have hT := WH.exists_disposal hDH γ hP.choose_spec.1
  { A := A0
    P := hP.choose
    T := hT.choose
    hT0 := hT.choose_spec.1
    hTP := hT.choose_spec.2.1
    hPA := hP.choose_spec.2.1
    hrejG := hP.choose_spec.2.2
    hrejH := hT.choose_spec.2.2 }

/-- The full run of Algorithm 1. -/
noncomputable def daSeq (hcG : Exchangeable WG.cFn)
    (hDG : ∀ μ ∈ WG.D, 0 ≤ μ) (hDH : ∀ μ ∈ WH.D, 0 ≤ μ)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) : ℕ → DAState WG WH α γ
  | 0 => daInit hDG hDH hA0
  | (k + 1) => daStep hcG hDH (daSeq hcG hDG hDH hA0 k)

theorem daSeq_cross (hcG : Exchangeable WG.cFn)
    (hDG : ∀ μ ∈ WG.D, 0 ≤ μ) (hDH : ∀ μ ∈ WH.D, 0 ≤ μ)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) (k : ℕ) :
    (daSeq hcG hDG hDH (α := α) (γ := γ) hA0 k).T ≤
      (daSeq hcG hDG hDH (α := α) (γ := γ) hA0 (k + 1)).P := by
  rw [show k + 1 = Nat.succ k by omega]
  simp only [daSeq]
  exact daStep_cross hcG hDH _

/-- **Proposition 3 (Algorithm 1 is well defined).** For exchangeable
proposer cost and welfare domains in the nonnegative orthant, Algorithm 1
runs forever from any nonnegative initial availability: there are sequences
satisfying the proposal, disposal, and update phases.  Packaged as a
`DASequences`, so availabilities converge and rejected masses vanish
(`DASequences.tendsto_A`, `DASequences.tendsto_sub_PT`). -/
theorem algorithm_wellDefined (hcG : Exchangeable WG.cFn)
    (hDG : ∀ μ ∈ WG.D, 0 ≤ μ) (hDH : ∀ μ ∈ WH.D, 0 ≤ μ)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) :
    ∃ s : DASequences ι, s.A 0 = A0 ∧
      (∀ k, s.A k - s.P k ∈ WG.rejectSet α (s.A k)) ∧
      (∀ k, s.P k - s.T k ∈ WH.rejectSet γ (s.P k)) ∧
      (∀ k, s.T k ≤ s.P (k + 1)) := by
  refine ⟨{ A := fun k => (daSeq hcG hDG hDH (α := α) (γ := γ) hA0 k).A
            P := fun k => (daSeq hcG hDG hDH (α := α) (γ := γ) hA0 k).P
            T := fun k => (daSeq hcG hDG hDH (α := α) (γ := γ) hA0 k).T
            nonneg_T := fun k => (daSeq hcG hDG hDH hA0 k).hT0
            T_le_P := fun k => (daSeq hcG hDG hDH hA0 k).hTP
            P_le_A := fun k => (daSeq hcG hDG hDH hA0 k).hPA
            update := fun k => rfl }, rfl,
    fun k => (daSeq hcG hDG hDH hA0 k).hrejG,
    fun k => (daSeq hcG hDG hDH hA0 k).hrejH,
    fun k => daSeq_cross hcG hDG hDH hA0 k⟩

end GHS
