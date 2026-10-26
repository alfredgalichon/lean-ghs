import GHS.ClassicalStability

/-!
# Classical one-to-one stable NTU matching

This file gives a paper-facing verification of GHS Proposition 3.1 and
Corollary 3.1 in the revised formulation. A one-to-one matching is represented
by mutually consistent partner maps. This is equivalent to the paper's binary
incidence vector with one assignment, including the outside option, in each
row and column.
-/

namespace GHS

variable {X Y : Type*}

/-- A one-to-one matching, with `none` denoting the outside option. -/
structure OneToOneMatching (X Y : Type*) where
  partnerX : X → Option Y
  partnerY : Y → Option X
  consistent : ∀ x y, partnerX x = some y ↔ partnerY y = some x

namespace OneToOneMatching

variable (M : OneToOneMatching X Y)

/-- Utility realized by an agent on the X side. -/
def realizedUtilityX (a0 : X → ℝ) (a : X → Y → ℝ) (x : X) : ℝ :=
  match M.partnerX x with
  | none => a0 x
  | some y => a x y

/-- Utility realized by an agent on the Y side. -/
def realizedUtilityY (g0 : Y → ℝ) (g : X → Y → ℝ) (y : Y) : ℝ :=
  match M.partnerY y with
  | none => g0 y
  | some x => g x y

section Incidence

/-- Binary incidence mass on a potential pair. -/
def pairMass [DecidableEq Y] (x : X) (y : Y) : ℝ :=
  if M.partnerX x = some y then 1 else 0

/-- Binary mass assigned to the outside option on the X side. -/
def unmatchedMassX [DecidableEq Y] (x : X) : ℝ :=
  if M.partnerX x = none then 1 else 0

/-- Binary mass assigned to the outside option on the Y side. -/
def unmatchedMassY [DecidableEq X] (y : Y) : ℝ :=
  if M.partnerY y = none then 1 else 0

theorem pairMass_zero_or_one [DecidableEq Y] (x : X) (y : Y) :
    M.pairMass x y = 0 ∨ M.pairMass x y = 1 := by
  by_cases h : M.partnerX x = some y
  · right; simp [pairMass, h]
  · left; simp [pairMass, h]

theorem unmatchedMassX_zero_or_one [DecidableEq Y] (x : X) :
    M.unmatchedMassX x = 0 ∨ M.unmatchedMassX x = 1 := by
  by_cases h : M.partnerX x = none
  · right; simp [unmatchedMassX, h]
  · left; simp [unmatchedMassX, h]

theorem unmatchedMassY_zero_or_one [DecidableEq X] (y : Y) :
    M.unmatchedMassY y = 0 ∨ M.unmatchedMassY y = 1 := by
  by_cases h : M.partnerY y = none
  · right; simp [unmatchedMassY, h]
  · left; simp [unmatchedMassY, h]

/-- The incidence vector has exactly one assignment in every row. -/
theorem row_incidence_sum [Fintype Y] [DecidableEq Y] (x : X) :
    (∑ y, M.pairMass x y) + M.unmatchedMassX x = 1 := by
  cases h : M.partnerX x with
  | none => simp [pairMass, unmatchedMassX, h]
  | some y => simp [pairMass, unmatchedMassX, h]

/-- The incidence vector has exactly one assignment in every column. -/
theorem column_incidence_sum [Fintype X] [DecidableEq X] [DecidableEq Y]
    (y : Y) :
    (∑ x, M.pairMass x y) + M.unmatchedMassY y = 1 := by
  cases h : M.partnerY y with
  | none => simp [pairMass, unmatchedMassY, h, M.consistent]
  | some x => simp [pairMass, unmatchedMassY, h, M.consistent]

end Incidence

/-- Classical individual rationality and absence of a blocking pair. -/
def IsStableNTU (a0 : X → ℝ) (g0 : Y → ℝ)
    (a g : X → Y → ℝ) : Prop :=
  (∀ x, a0 x ≤ M.realizedUtilityX a0 a x) ∧
  (∀ y, g0 y ≤ M.realizedUtilityY g0 g y) ∧
  (∀ x y, 0 ≤ max (M.realizedUtilityX a0 a x - a x y)
    (M.realizedUtilityY g0 g y - g x y))

/-- The assignment selected by `M` maximizes the adjusted utility of every
agent on the X side. -/
def XChooses (a0 : X → ℝ) (U : X → Y → ℝ) : Prop :=
  (∀ x, M.partnerX x = none → ∀ y, U x y ≤ a0 x) ∧
  (∀ x y, M.partnerX x = some y →
    a0 x ≤ U x y ∧ ∀ y', U x y' ≤ U x y)

/-- The assignment selected by `M` maximizes the adjusted utility of every
agent on the Y side. -/
def YChooses (g0 : Y → ℝ) (V : X → Y → ℝ) : Prop :=
  (∀ y, M.partnerY y = none → ∀ x, V x y ≤ g0 y) ∧
  (∀ x y, M.partnerY y = some x →
    g0 y ≤ V x y ∧ ∀ x', V x' y ≤ V x y)

/-- The matching has an equilibrium representation with a burn-only frontier. -/
def HasEquilibriumRepresentation (a0 : X → ℝ) (g0 : Y → ℝ)
    (a g : X → Y → ℝ) : Prop :=
  ∃ U V : X → Y → ℝ,
    M.XChooses a0 U ∧ M.YChooses g0 V ∧
      ∀ x y, max (U x y - a x y) (V x y - g x y) = 0

private theorem max_min_sub_eq_zero {u a v g : ℝ}
    (hstable : 0 ≤ max (u - a) (v - g)) :
    max (min u a - a) (min v g - g) = 0 := by
  rcases le_total u a with hua | hau
  · rcases le_total v g with hvg | hgv
    · rw [min_eq_left hua, min_eq_left hvg]
      exact le_antisymm (max_le (sub_nonpos.mpr hua) (sub_nonpos.mpr hvg)) hstable
    · rw [min_eq_left hua, min_eq_right hgv]
      simp [sub_self, max_eq_right (sub_nonpos.mpr hua)]
  · rw [min_eq_right hau]
    simp [sub_self]

/-- **GHS Proposition 3.1.** A classical one-to-one NTU matching is stable if
and only if it has an equilibrium representation with a burn-only frontier. -/
theorem stableNTU_iff_hasEquilibriumRepresentation
    (a0 : X → ℝ) (g0 : Y → ℝ) (a g : X → Y → ℝ) :
    M.IsStableNTU a0 g0 a g ↔ M.HasEquilibriumRepresentation a0 g0 a g := by
  constructor
  · rintro ⟨hIRX, hIRY, hstable⟩
    let U : X → Y → ℝ := fun x y => min (M.realizedUtilityX a0 a x) (a x y)
    let V : X → Y → ℝ := fun x y => min (M.realizedUtilityY g0 g y) (g x y)
    refine ⟨U, V, ?_, ?_, ?_⟩
    · constructor
      · intro x hx y
        simp [U, realizedUtilityX, hx]
      · intro x y hxy
        constructor
        · simpa [U, realizedUtilityX, hxy] using hIRX x
        · intro y'
          simp [U, realizedUtilityX, hxy]
    · constructor
      · intro y hy x
        simp [V, realizedUtilityY, hy]
      · intro x y hxy
        constructor
        · simpa [V, realizedUtilityY, hxy] using hIRY y
        · intro x'
          simp [V, realizedUtilityY, hxy]
    · intro x y
      exact max_min_sub_eq_zero (hstable x y)
  · rintro ⟨U, V, hchooseX, hchooseY, hfrontier⟩
    have hUle : ∀ x y, U x y ≤ M.realizedUtilityX a0 a x := by
      intro x y
      cases hpx : M.partnerX x with
      | none =>
          simpa [realizedUtilityX, hpx] using hchooseX.1 x hpx y
      | some y0 =>
          have hchoice := (hchooseX.2 x y0 hpx).2 y
          have hfront := hfrontier x y0
          have hused : U x y0 ≤ a x y0 := by
            have h := le_max_left (U x y0 - a x y0) (V x y0 - g x y0)
            rw [hfront] at h
            linarith
          calc
            U x y ≤ U x y0 := hchoice
            _ ≤ M.realizedUtilityX a0 a x := by
              simpa [realizedUtilityX, hpx] using hused
    have hVle : ∀ x y, V x y ≤ M.realizedUtilityY g0 g y := by
      intro x y
      cases hpy : M.partnerY y with
      | none =>
          simpa [realizedUtilityY, hpy] using hchooseY.1 y hpy x
      | some x0 =>
          have hchoice := (hchooseY.2 x0 y hpy).2 x
          have hfront := hfrontier x0 y
          have hused : V x0 y ≤ g x0 y := by
            have h := le_max_right (U x0 y - a x0 y) (V x0 y - g x0 y)
            rw [hfront] at h
            linarith
          calc
            V x y ≤ V x0 y := hchoice
            _ ≤ M.realizedUtilityY g0 g y := by
              simpa [realizedUtilityY, hpy] using hused
    refine ⟨?_, ?_, ?_⟩
    · intro x
      cases hpx : M.partnerX x with
      | none => simp [realizedUtilityX, hpx]
      | some y =>
          have hout := (hchooseX.2 x y hpx).1
          have hfront := hfrontier x y
          have hused : U x y ≤ a x y := by
            have h := le_max_left (U x y - a x y) (V x y - g x y)
            rw [hfront] at h
            linarith
          simpa [realizedUtilityX, hpx] using le_trans hout hused
    · intro y
      cases hpy : M.partnerY y with
      | none => simp [realizedUtilityY, hpy]
      | some x =>
          have hout := (hchooseY.2 x y hpy).1
          have hfront := hfrontier x y
          have hused : V x y ≤ g x y := by
            have h := le_max_right (U x y - a x y) (V x y - g x y)
            rw [hfront] at h
            linarith
          simpa [realizedUtilityY, hpy] using le_trans hout hused
    · intro x y
      have hmono : max (U x y - a x y) (V x y - g x y) ≤
          max (M.realizedUtilityX a0 a x - a x y)
            (M.realizedUtilityY g0 g y - g x y) :=
        max_le_max (sub_le_sub_right (hUle x y) _)
          (sub_le_sub_right (hVle x y) _)
      rw [hfrontier x y] at hmono
      exact hmono

/-- **GHS Corollary 3.1.** For deterministic one-to-one welfare, aggregate
equilibrium matching is equivalent to classical stable NTU matching. -/
theorem aggregateEquilibrium_iff_stableNTU
    (a0 : X → ℝ) (g0 : Y → ℝ) (a g : X → Y → ℝ) :
    M.HasEquilibriumRepresentation a0 g0 a g ↔ M.IsStableNTU a0 g0 a g :=
  (M.stableNTU_iff_hasEquilibriumRepresentation a0 g0 a g).symm

end OneToOneMatching

end GHS
