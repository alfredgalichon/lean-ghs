import GHS.RandomUtility

/-!
# Classical stable NTU matching and deterministic welfare

This file retains the auxiliary aggregate-mass formulation used in an earlier
draft. The deterministic subgradient conditions are expanded into their
standard finite-maximum form: nonnegative masses, capacity bounds, support on
maximizing alternatives, and use of the outside option whenever capacity is
slack. The exact one-to-one statements of revised GHS Proposition 3.1 and
Corollary 3.1 are verified in `ClassicalStableBinary.lean`.
-/

namespace GHS

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Classical stable NTU data, including pair masses and unmatched masses. -/
structure ClassicalStableNTU
    (n : X → ℝ) (m : Y → ℝ)
    (a0 : X → ℝ) (g0 : Y → ℝ)
    (a g : X → Y → ℝ) where
  pairMass : X → Y → ℝ
  unmatchedX : X → ℝ
  unmatchedY : Y → ℝ
  utilityX : X → ℝ
  utilityY : Y → ℝ
  pair_nonneg : ∀ x y, 0 ≤ pairMass x y
  unmatchedX_nonneg : ∀ x, 0 ≤ unmatchedX x
  unmatchedY_nonneg : ∀ y, 0 ≤ unmatchedY y
  row_feasible : ∀ x, (∑ y, pairMass x y) + unmatchedX x = n x
  column_feasible : ∀ y, (∑ x, pairMass x y) + unmatchedY y = m y
  individually_rational_X : ∀ x, a0 x ≤ utilityX x
  individually_rational_Y : ∀ y, g0 y ≤ utilityY y
  pairwise_stable : ∀ x y,
    0 ≤ max (utilityX x - a x y) (utilityY y - g x y)
  used_pair_complementary : ∀ x y, 0 < pairMass x y →
    max (utilityX x - a x y) (utilityY y - g x y) = 0
  unmatchedX_complementary : ∀ x, 0 < unmatchedX x → utilityX x = a0 x
  unmatchedY_complementary : ∀ y, 0 < unmatchedY y → utilityY y = g0 y

/-- The deterministic welfare representation after expanding membership in
the two subdifferentials of the finite-maximum welfare functions. -/
structure ClassicalWelfareRepresentation
    (n : X → ℝ) (m : Y → ℝ)
    (a0 : X → ℝ) (g0 : Y → ℝ)
    (a g : X → Y → ℝ) where
  pairMass : X → Y → ℝ
  U : X → Y → ℝ
  V : X → Y → ℝ
  rowUtility : X → ℝ
  columnUtility : Y → ℝ
  pair_nonneg : ∀ x y, 0 ≤ pairMass x y
  row_capacity : ∀ x, (∑ y, pairMass x y) ≤ n x
  column_capacity : ∀ y, (∑ x, pairMass x y) ≤ m y
  row_outside_le : ∀ x, a0 x ≤ rowUtility x
  column_outside_le : ∀ y, g0 y ≤ columnUtility y
  row_alternative_le : ∀ x y, U x y ≤ rowUtility x
  column_alternative_le : ∀ x y, V x y ≤ columnUtility y
  row_used_maximizer : ∀ x y, 0 < pairMass x y → U x y = rowUtility x
  column_used_maximizer : ∀ x y, 0 < pairMass x y → V x y = columnUtility y
  row_slack_outside : ∀ x, (∑ y, pairMass x y) < n x → rowUtility x = a0 x
  column_slack_outside : ∀ y, (∑ x, pairMass x y) < m y →
    columnUtility y = g0 y
  burnOnlyFrontier : ∀ x y, max (U x y - a x y) (V x y - g x y) = 0

private theorem max_min_sub_eq_zero {u a v g : ℝ}
    (hstable : 0 ≤ max (u - a) (v - g)) :
    max (min u a - a) (min v g - g) = 0 := by
  rcases le_total u a with hua | hau
  · rcases le_total v g with hvg | hgv
    · rw [min_eq_left hua, min_eq_left hvg]
      have hmax : max (u - a) (v - g) ≤ 0 :=
        max_le (sub_nonpos.mpr hua) (sub_nonpos.mpr hvg)
      exact le_antisymm hmax hstable
    · rw [min_eq_left hua, min_eq_right hgv]
      simp [sub_self, max_eq_right (sub_nonpos.mpr hua)]
  · rw [min_eq_right hau]
    simp [sub_self]

/-- In the auxiliary aggregate-mass formulation, stable NTU data exist
exactly when the deterministic welfare representation exists. -/
theorem classicalStableNTU_nonempty_iff_welfareRepresentation_nonempty
    (n : X → ℝ) (m : Y → ℝ)
    (a0 : X → ℝ) (g0 : Y → ℝ)
    (a g : X → Y → ℝ) :
    Nonempty (ClassicalStableNTU n m a0 g0 a g) ↔
      Nonempty (ClassicalWelfareRepresentation n m a0 g0 a g) := by
  constructor
  · rintro ⟨S⟩
    let U : X → Y → ℝ := fun x y => min (S.utilityX x) (a x y)
    let V : X → Y → ℝ := fun x y => min (S.utilityY y) (g x y)
    refine ⟨{
      pairMass := S.pairMass
      U := U
      V := V
      rowUtility := S.utilityX
      columnUtility := S.utilityY
      pair_nonneg := S.pair_nonneg
      row_capacity := ?_
      column_capacity := ?_
      row_outside_le := S.individually_rational_X
      column_outside_le := S.individually_rational_Y
      row_alternative_le := ?_
      column_alternative_le := ?_
      row_used_maximizer := ?_
      column_used_maximizer := ?_
      row_slack_outside := ?_
      column_slack_outside := ?_
      burnOnlyFrontier := ?_ }⟩
    · intro x
      linarith [S.row_feasible x, S.unmatchedX_nonneg x]
    · intro y
      linarith [S.column_feasible y, S.unmatchedY_nonneg y]
    · intro x y
      exact min_le_left _ _
    · intro x y
      exact min_le_left _ _
    · intro x y hxy
      have hc := S.used_pair_complementary x y hxy
      have hle : S.utilityX x ≤ a x y := by
        have h := le_max_left (S.utilityX x - a x y) (S.utilityY y - g x y)
        rw [hc] at h
        linarith
      exact min_eq_left hle
    · intro x y hxy
      have hc := S.used_pair_complementary x y hxy
      have hle : S.utilityY y ≤ g x y := by
        have h := le_max_right (S.utilityX x - a x y) (S.utilityY y - g x y)
        rw [hc] at h
        linarith
      exact min_eq_left hle
    · intro x hx
      have hpos : 0 < S.unmatchedX x := by
        linarith [S.row_feasible x]
      exact S.unmatchedX_complementary x hpos
    · intro y hy
      have hpos : 0 < S.unmatchedY y := by
        linarith [S.column_feasible y]
      exact S.unmatchedY_complementary y hpos
    · intro x y
      exact max_min_sub_eq_zero (S.pairwise_stable x y)
  · rintro ⟨W⟩
    let ux0 : X → ℝ := fun x => n x - ∑ y, W.pairMass x y
    let u0y : Y → ℝ := fun y => m y - ∑ x, W.pairMass x y
    refine ⟨{
      pairMass := W.pairMass
      unmatchedX := ux0
      unmatchedY := u0y
      utilityX := W.rowUtility
      utilityY := W.columnUtility
      pair_nonneg := W.pair_nonneg
      unmatchedX_nonneg := ?_
      unmatchedY_nonneg := ?_
      row_feasible := ?_
      column_feasible := ?_
      individually_rational_X := W.row_outside_le
      individually_rational_Y := W.column_outside_le
      pairwise_stable := ?_
      used_pair_complementary := ?_
      unmatchedX_complementary := ?_
      unmatchedY_complementary := ?_ }⟩
    · intro x
      exact sub_nonneg.mpr (W.row_capacity x)
    · intro y
      exact sub_nonneg.mpr (W.column_capacity y)
    · intro x
      simp [ux0]
    · intro y
      simp [u0y]
    · intro x y
      have hmono : max (W.U x y - a x y) (W.V x y - g x y) ≤
          max (W.rowUtility x - a x y) (W.columnUtility y - g x y) :=
        max_le_max (sub_le_sub_right (W.row_alternative_le x y) _)
          (sub_le_sub_right (W.column_alternative_le x y) _)
      rw [W.burnOnlyFrontier x y] at hmono
      exact hmono
    · intro x y hxy
      rw [← W.row_used_maximizer x y hxy, ← W.column_used_maximizer x y hxy]
      exact W.burnOnlyFrontier x y
    · intro x hx
      apply W.row_slack_outside x
      have hpos : 0 < n x - ∑ y, W.pairMass x y := by simpa [ux0] using hx
      linarith
    · intro y hy
      apply W.column_slack_outside y
      have hpos : 0 < m y - ∑ x, W.pairMass x y := by simpa [u0y] using hy
      linarith

/-- Deterministic burn-only equilibrium data are exactly the deterministic
welfare representation used above. -/
abbrev DeterministicBurnOnlyEquilibrium
    (n : X → ℝ) (m : Y → ℝ)
    (a0 : X → ℝ) (g0 : Y → ℝ)
    (a g : X → Y → ℝ) :=
  ClassicalWelfareRepresentation n m a0 g0 a g

/-- With deterministic finite-maximum welfare, the auxiliary burn-only
formulation exists exactly when the aggregate stable NTU data exist. -/
theorem deterministicBurnOnly_nonempty_iff_classicalStableNTU_nonempty
    (n : X → ℝ) (m : Y → ℝ)
    (a0 : X → ℝ) (g0 : Y → ℝ)
    (a g : X → Y → ℝ) :
    Nonempty (DeterministicBurnOnlyEquilibrium n m a0 g0 a g) ↔
      Nonempty (ClassicalStableNTU n m a0 g0 a g) :=
  (classicalStableNTU_nonempty_iff_welfareRepresentation_nonempty
    n m a0 g0 a g).symm

end GHS
