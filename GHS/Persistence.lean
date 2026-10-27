import GHS.WelfareData
import GHS.Theorem3

/-!
# Persistence of welfare-generated choices

This file supplies machine-checked counterparts of the two assertions in the
paper's persistence proposition.  The first part gives an explicit continuous
and consistent selection from the box `[0, b \inf 1]` and verifies the stated
failure of persistence.  The second part isolates the order argument used for
point-valued welfare choices: contraction consistency and monotonicity of
rejections imply persistence.  The welfare-choice hypotheses in the paper
supply these two properties.
-/

namespace GHS

/-! ## A continuous consistent selection that is not persistent -/

/-- Availability capped at one, coordinate by coordinate. -/
def capOne (x : ℝ) : ℝ := min x 1

/-- The explicit form of the quadratic tie-breaking selection used in the
paper's two-coordinate counterexample. -/
noncomputable def persistenceCounterexampleChoice (b : ℝ × ℝ) : ℝ × ℝ :=
  (min (capOne b.1) ((capOne b.2 + 1) / 2),
   min (capOne b.2) ((capOne b.1 + 1) / 2))

/-- The strictly concave objective in the paper's persistence counterexample. -/
def persistenceCounterexampleObjective (q : ℝ × ℝ) : ℝ :=
  -((q.1 - q.2) ^ 2 + (q.1 - 1) ^ 2 + (q.2 - 1) ^ 2)

theorem capOne_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ capOne x := by
  exact le_min hx zero_le_one

theorem capOne_le_self (x : ℝ) : capOne x ≤ x := min_le_left _ _

theorem capOne_le_one (x : ℝ) : capOne x ≤ 1 := min_le_right _ _

theorem capOne_mono {x y : ℝ} (hxy : x ≤ y) : capOne x ≤ capOne y := by
  exact min_le_min hxy le_rfl

theorem persistenceCounterexampleChoice_mem_box {b : ℝ × ℝ}
    (hb : 0 ≤ b.1 ∧ 0 ≤ b.2) :
    0 ≤ (persistenceCounterexampleChoice b).1 ∧
      (persistenceCounterexampleChoice b).1 ≤ capOne b.1 ∧
    0 ≤ (persistenceCounterexampleChoice b).2 ∧
      (persistenceCounterexampleChoice b).2 ≤ capOne b.2 := by
  have hA0 : 0 ≤ capOne b.1 := capOne_nonneg hb.1
  have hB0 : 0 ≤ capOne b.2 := capOne_nonneg hb.2
  dsimp [persistenceCounterexampleChoice]
  constructor
  · exact le_min hA0 (by linarith)
  constructor
  · exact min_le_left _ _
  constructor
  · exact le_min hB0 (by linarith)
  · exact min_le_left _ _

/-- The displayed closed form is indeed a maximizer of the paper's strictly
concave quadratic objective over the capped availability box. -/
theorem persistenceCounterexampleChoice_maximizes {b q : ℝ × ℝ}
    (hb : 0 ≤ b.1 ∧ 0 ≤ b.2)
    (hq : 0 ≤ q.1 ∧ q.1 ≤ capOne b.1 ∧
      0 ≤ q.2 ∧ q.2 ≤ capOne b.2) :
    persistenceCounterexampleObjective q ≤
      persistenceCounterexampleObjective (persistenceCounterexampleChoice b) := by
  let A := capOne b.1
  let B := capOne b.2
  have hA0 : 0 ≤ A := capOne_nonneg hb.1
  have hB0 : 0 ≤ B := capOne_nonneg hb.2
  have hA1 : A ≤ 1 := capOne_le_one _
  have hB1 : B ≤ 1 := capOne_le_one _
  change persistenceCounterexampleObjective q ≤
    persistenceCounterexampleObjective
      (min A ((B + 1) / 2), min B ((A + 1) / 2))
  by_cases hA : A ≤ (B + 1) / 2
  · by_cases hB : B ≤ (A + 1) / 2
    · have hx : q.1 - A ≤ 0 := by linarith [hq.2.1]
      have hy : q.2 - B ≤ 0 := by linarith [hq.2.2.2]
      have hgx : 4 * A - 2 * B - 2 ≤ 0 := by linarith
      have hgy : 4 * B - 2 * A - 2 ≤ 0 := by linarith
      have hxg : 0 ≤ (q.1 - A) * (4 * A - 2 * B - 2) :=
        mul_nonneg_of_nonpos_of_nonpos hx hgx
      have hyg : 0 ≤ (q.2 - B) * (4 * B - 2 * A - 2) :=
        mul_nonneg_of_nonpos_of_nonpos hy hgy
      have hs1 : 0 ≤ (q.1 - A - (q.2 - B)) ^ 2 := sq_nonneg _
      have hs2 : 0 ≤ (q.1 - A) ^ 2 := sq_nonneg _
      have hs3 : 0 ≤ (q.2 - B) ^ 2 := sq_nonneg _
      rw [min_eq_left hA, min_eq_left hB]
      unfold persistenceCounterexampleObjective
      dsimp
      nlinarith
    · have hB' : (A + 1) / 2 ≤ B := le_of_not_ge hB
      have hx : q.1 - A ≤ 0 := by linarith [hq.2.1]
      have hgx : 3 * (A - 1) ≤ 0 := by linarith
      have hxg : 0 ≤ (q.1 - A) * (3 * (A - 1)) :=
        mul_nonneg_of_nonpos_of_nonpos hx hgx
      have hs1 : 0 ≤ (q.1 - A - (q.2 - (A + 1) / 2)) ^ 2 := sq_nonneg _
      have hs2 : 0 ≤ (q.1 - A) ^ 2 := sq_nonneg _
      have hs3 : 0 ≤ (q.2 - (A + 1) / 2) ^ 2 := sq_nonneg _
      rw [min_eq_left hA, min_eq_right hB']
      unfold persistenceCounterexampleObjective
      dsimp
      nlinarith
  · have hA' : (B + 1) / 2 ≤ A := le_of_not_ge hA
    by_cases hB : B ≤ (A + 1) / 2
    · have hy : q.2 - B ≤ 0 := by linarith [hq.2.2.2]
      have hgy : 3 * (B - 1) ≤ 0 := by linarith
      have hyg : 0 ≤ (q.2 - B) * (3 * (B - 1)) :=
        mul_nonneg_of_nonpos_of_nonpos hy hgy
      have hs1 : 0 ≤ (q.1 - (B + 1) / 2 - (q.2 - B)) ^ 2 := sq_nonneg _
      have hs2 : 0 ≤ (q.1 - (B + 1) / 2) ^ 2 := sq_nonneg _
      have hs3 : 0 ≤ (q.2 - B) ^ 2 := sq_nonneg _
      rw [min_eq_right hA', min_eq_left hB]
      unfold persistenceCounterexampleObjective
      dsimp
      nlinarith
    · have hB' : (A + 1) / 2 ≤ B := le_of_not_ge hB
      exfalso
      linarith [hA0, hB0]

theorem continuous_persistenceCounterexampleChoice :
    Continuous persistenceCounterexampleChoice := by
  unfold persistenceCounterexampleChoice capOne
  fun_prop

/-- The scalar calculation behind contraction consistency of the explicit
selection. -/
theorem first_coordinate_consistent
    {A B A' B' : ℝ}
    (hA1 : A ≤ 1) (hB1 : B ≤ 1)
    (hAA' : A ≤ A') (hBB' : B ≤ B')
    (hx : min A' ((B' + 1) / 2) ≤ A)
    (hy : min B' ((A' + 1) / 2) ≤ B) :
    min A ((B + 1) / 2) = min A' ((B' + 1) / 2) := by
  by_cases hAcase : A' ≤ (B' + 1) / 2
  · have hxval : min A' ((B' + 1) / 2) = A' := min_eq_left hAcase
    have hAA : A = A' := by
      rw [hxval] at hx
      linarith
    have hAtB : A ≤ (B + 1) / 2 := by
      by_cases hBcase : B' ≤ (A' + 1) / 2
      · have hyval : min B' ((A' + 1) / 2) = B' := min_eq_left hBcase
        rw [hyval] at hy
        have hBB : B = B' := by linarith
        rw [hAA, hBB]
        exact hAcase
      · have hBcase' : (A' + 1) / 2 ≤ B' := le_of_not_ge hBcase
        have hyval : min B' ((A' + 1) / 2) = (A' + 1) / 2 :=
          min_eq_right hBcase'
        rw [hyval, ← hAA] at hy
        linarith
    rw [min_eq_left hAtB, hxval, hAA]
  · have hAcase' : (B' + 1) / 2 ≤ A' := le_of_not_ge hAcase
    have hxval : min A' ((B' + 1) / 2) = (B' + 1) / 2 :=
      min_eq_right hAcase'
    have hBB : B = B' := by
      by_cases hBcase : B' ≤ (A' + 1) / 2
      · have hyval : min B' ((A' + 1) / 2) = B' := min_eq_left hBcase
        rw [hyval] at hy
        linarith
      · have hBcase' : (A' + 1) / 2 ≤ B' := le_of_not_ge hBcase
        have hyval : min B' ((A' + 1) / 2) = (A' + 1) / 2 :=
          min_eq_right hBcase'
        rw [hyval] at hy
        have hstrict : (B' + 1) / 2 < A' := lt_of_not_ge hAcase
        linarith
    rw [hxval, hBB]
    have hBA : (B' + 1) / 2 ≤ A := by
      rw [hxval] at hx
      exact hx
    exact min_eq_right hBA

theorem persistenceCounterexampleChoice_consistent
    {b b' : ℝ × ℝ}
    (hb0 : 0 ≤ b.1 ∧ 0 ≤ b.2)
    (hbb' : b.1 ≤ b'.1 ∧ b.2 ≤ b'.2)
    (hchoice :
      (persistenceCounterexampleChoice b').1 ≤ b.1 ∧
      (persistenceCounterexampleChoice b').2 ≤ b.2) :
    persistenceCounterexampleChoice b = persistenceCounterexampleChoice b' := by
  let A := capOne b.1
  let B := capOne b.2
  let A' := capOne b'.1
  let B' := capOne b'.2
  have hA0 : 0 ≤ A := capOne_nonneg hb0.1
  have hB0 : 0 ≤ B := capOne_nonneg hb0.2
  have hb'0 : 0 ≤ b'.1 ∧ 0 ≤ b'.2 := ⟨le_trans hb0.1 hbb'.1, le_trans hb0.2 hbb'.2⟩
  have hA'0 : 0 ≤ A' := capOne_nonneg hb'0.1
  have hB'0 : 0 ≤ B' := capOne_nonneg hb'0.2
  have hA1 : A ≤ 1 := capOne_le_one _
  have hB1 : B ≤ 1 := capOne_le_one _
  have hA'1 : A' ≤ 1 := capOne_le_one _
  have hB'1 : B' ≤ 1 := capOne_le_one _
  have hAA' : A ≤ A' := capOne_mono hbb'.1
  have hBB' : B ≤ B' := capOne_mono hbb'.2
  have hxone : (persistenceCounterexampleChoice b').1 ≤ 1 := by
    exact le_trans (min_le_left _ _) hA'1
  have hyone : (persistenceCounterexampleChoice b').2 ≤ 1 := by
    exact le_trans (min_le_left _ _) hB'1
  have hx : min A' ((B' + 1) / 2) ≤ A := by
    change (persistenceCounterexampleChoice b').1 ≤ capOne b.1
    exact le_min hchoice.1 hxone
  have hy : min B' ((A' + 1) / 2) ≤ B := by
    change (persistenceCounterexampleChoice b').2 ≤ capOne b.2
    exact le_min hchoice.2 hyone
  apply Prod.ext
  · exact first_coordinate_consistent hA1 hB1
      hAA' hBB' hx hy
  · exact first_coordinate_consistent hB1 hA1
      hBB' hAA' hy hx

theorem persistenceCounterexampleChoice_values :
    persistenceCounterexampleChoice (1, (1 : ℝ) / 2) = ((3 : ℝ) / 4, (1 : ℝ) / 2) ∧
    persistenceCounterexampleChoice (1, 1) = (1, 1) := by
  norm_num [persistenceCounterexampleChoice, capOne, min_def]

theorem persistenceCounterexampleChoice_not_persistent :
    ¬ ((min (persistenceCounterexampleChoice (1, 1)).1 (1 : ℝ),
        min (persistenceCounterexampleChoice (1, 1)).2 ((1 : ℝ) / 2)).1 ≤
          (persistenceCounterexampleChoice (1, (1 : ℝ) / 2)).1 ∧
       (min (persistenceCounterexampleChoice (1, 1)).1 (1 : ℝ),
        min (persistenceCounterexampleChoice (1, 1)).2 ((1 : ℝ) / 2)).2 ≤
          (persistenceCounterexampleChoice (1, (1 : ℝ) / 2)).2) := by
  norm_num [persistenceCounterexampleChoice, capOne, min_def]

/-! ## Point-valued choices are persistent -/

/-- The order-theoretic core of the paper's point-valued persistence result.
For welfare-generated singleton choices, contraction consistency is immediate
from optimality, and rejection monotonicity is the singleton specialization of
the capacity comparative-statics theorem. -/
theorem persistent_of_consistent_rejectionMonotone
    {ι : Type*} (C : (ι → ℝ) → (ι → ℝ))
    (hfeas : ∀ b, 0 ≤ b → C b ≤ b)
    (hconsistent : ∀ b b', 0 ≤ b → b ≤ b' → C b' ≤ b → C b = C b')
    (hrejection : ∀ b b', 0 ≤ b → b ≤ b' → b - C b ≤ b' - C b')
    {b b' : ι → ℝ} (hb0 : 0 ≤ b) (hbb' : b ≤ b') :
    C b' ⊓ b ≤ C b := by
  have hb'0 : 0 ≤ b' := le_trans hb0 hbb'
  let t : ι → ℝ := b ⊔ C b'
  have ht0 : 0 ≤ t := le_trans hb0 le_sup_left
  have httop : t ≤ b' := sup_le hbb' (hfeas b' hb'0)
  have hCt : C t = C b' :=
    hconsistent t b' ht0 httop le_sup_right
  have hr := hrejection b t hb0 le_sup_left
  rw [hCt] at hr
  intro i
  have hri := hr i
  change min (C b' i) (b i) ≤ C b i
  change b i - C b i ≤ max (b i) (C b' i) - C b' i at hri
  by_cases h : C b' i ≤ b i
  · rw [min_eq_left h, max_eq_left h] at *
    linarith
  · have h' : b i ≤ C b' i := le_of_not_ge h
    rw [min_eq_right h', max_eq_right h'] at *
    linarith

/-- Version stated directly with the singleton Q-order on rejected quantities,
which is the output of the paper's capacity comparative-statics theorem. -/
theorem persistent_of_consistent_qOrderedRejections
    {ι : Type*} (C : (ι → ℝ) → (ι → ℝ))
    (hfeas : ∀ b, 0 ≤ b → C b ≤ b)
    (hconsistent : ∀ b b', 0 ≤ b → b ≤ b' → C b' ≤ b → C b = C b')
    (hq : ∀ b b', 0 ≤ b → b ≤ b' →
      QOrderSet ({b - C b} : Set (ι → ℝ)) ({b' - C b'} : Set (ι → ℝ)))
    {b b' : ι → ℝ} (hb0 : 0 ≤ b) (hbb' : b ≤ b') :
    C b' ⊓ b ≤ C b := by
  apply persistent_of_consistent_rejectionMonotone C hfeas hconsistent
  · intro a a' ha0 haa'
    exact (qOrderSet_singleton_iff (a - C a) (a' - C a')).mp
      (hq a a' ha0 haa')
  · exact hb0
  · exact hbb'

/-- A point-valued welfare choice is persistent. Here `hchoice` states that
`C b` maximizes the welfare objective on the box with capacity `b`, in the
equivalent rejection formulation, and `hunique` states point-valuedness.
Both contraction consistency and the singleton Q-order used above are derived
inside the proof. -/
theorem persistent_of_unique_welfareMaximization
    {ι : Type*} [Fintype ι] (W : WelfareDual ι)
    (hc : Exchangeable W.cFn) (p : ι → ℝ)
    (C : (ι → ℝ) → (ι → ℝ))
    (hchoice : ∀ b, 0 ≤ b → b - C b ∈ W.rejectSet p b)
    (hunique : ∀ b, 0 ≤ b → ∀ r ∈ W.rejectSet p b, r = b - C b)
    {b b' : ι → ℝ} (hb0 : 0 ≤ b) (hbb' : b ≤ b') :
    C b' ⊓ b ≤ C b := by
  have hfeas : ∀ a, 0 ≤ a → C a ≤ a := by
    intro a ha0 i
    have hr0 := ((W.mem_rejectSet_iff_acceptance ha0).mp
      (hchoice a ha0)).1 i
    change 0 ≤ a i - C a i at hr0
    linarith
  have hconsistent : ∀ a a', 0 ≤ a → a ≤ a' → C a' ≤ a → C a = C a' := by
    intro a a' ha0 haa' hCa'
    have ha'0 : 0 ≤ a' := le_trans ha0 haa'
    obtain ⟨-, hCD, hopt⟩ :=
      (W.mem_rejectSet_iff_acceptance ha'0).mp (hchoice a' ha'0)
    have hcancel : a' - (a' - C a') = C a' := by
      funext i
      dsimp
      ring
    rw [hcancel] at hCD hopt
    have hr : a - C a' ∈ W.rejectSet p a := by
      apply (W.mem_rejectSet_iff_acceptance ha0).mpr
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have := hCa' i
        change 0 ≤ a i - C a' i
        linarith
      · simpa only [sub_sub_cancel]
      · intro ν hν hνa
        simpa only [sub_sub_cancel] using hopt ν hν (le_trans hνa haa')
    have heq := hunique a ha0 (a - C a') hr
    have : a - C a' = a - C a := heq
    funext i
    have hi := congrFun this i
    change a i - C a' i = a i - C a i at hi
    linarith
  have hq : ∀ a a', 0 ≤ a → a ≤ a' →
      QOrderSet ({a - C a} : Set (ι → ℝ)) ({a' - C a'} : Set (ι → ℝ)) := by
    intro a a' ha0 haa'
    have ha'0 : 0 ≤ a' := le_trans ha0 haa'
    have hset : W.rejectSet p a = ({a - C a} : Set (ι → ℝ)) := by
      ext r
      constructor
      · intro hr
        simpa only [Set.mem_singleton_iff] using hunique a ha0 r hr
      · intro hr
        have hr' : r = a - C a := Set.mem_singleton_iff.mp hr
        rw [hr']
        exact hchoice a ha0
    have hset' : W.rejectSet p a' = ({a' - C a'} : Set (ι → ℝ)) := by
      ext r
      constructor
      · intro hr
        simpa only [Set.mem_singleton_iff] using hunique a' ha'0 r hr
      · intro hr
        have hr' : r = a' - C a' := Set.mem_singleton_iff.mp hr
        rw [hr']
        exact hchoice a' ha'0
    rw [← hset, ← hset']
    exact qOrderSet_capacity hc p haa'
      (W.obj_finite_somewhere p ha0) (W.obj_finite_somewhere p ha'0)
  exact persistent_of_consistent_qOrderedRejections C hfeas hconsistent hq
    (b := b) (b' := b') hb0 hbb'

end GHS
