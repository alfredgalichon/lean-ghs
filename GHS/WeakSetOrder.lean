import GHS.BoxCalculus
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Group.Basic

/-!
# GHS Phase 2: the Q-order implies the weak set order (Proposition 2)

`GHS.qOrderSet_weakSetOrder` formalizes **Proposition 2**
(`prop:qorderimplieswso`): for closed *nonempty* `Q, Q'` with `Q ≤_Q Q'`,
one has `Q ≤_wso Q'` in the weak set order of Che–Kim–Kojima.

Note the nonemptiness hypotheses: the paper omits them, but the statement is
false for `Q ≠ ∅ = Q'` (the Q-order is vacuously true, the weak set order
fails) — recorded as erratum G11.

The proof is the paper's, made precise: pick the ℓ¹-nearest point of the other
set (attained because closed sets in `ι → ℝ` meet closed balls in compacta),
then apply the exchange property with the *extreme* perturbation
`δ₁ = (q - q')⁺`; the exchanged point is ℓ¹-closer by exactly
`∑ i, (q - q')⁺ i` (lemma `abs_transfer` coordinatewise), so optimality forces
`(q - q')⁺ = 0`, i.e. `q ≤ q'`.
-/

open Set Metric

namespace GHS

variable {ι : Type*}

/-- The weak set order of Che–Kim–Kojima: every point of `Q` is below some
point of `Q'`, and every point of `Q'` is above some point of `Q`. -/
def WeakSetOrder (Q Q' : Set (ι → ℝ)) : Prop :=
  (∀ q ∈ Q, ∃ q' ∈ Q', q ≤ q') ∧ (∀ q' ∈ Q', ∃ q ∈ Q, q ≤ q')

variable [Fintype ι]

/-! ## ℓ¹ distance and attainment -/

/-- The ℓ¹ distance from `z` to the anchor `t`. -/
def l1Dist (t z : ι → ℝ) : ℝ := ∑ i, |z i - t i|

theorem l1Dist_nonneg (t z : ι → ℝ) : 0 ≤ l1Dist t z :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_l1Dist (t : ι → ℝ) : Continuous (l1Dist t) :=
  continuous_finset_sum _ fun i _ => ((continuous_apply i).sub continuous_const).abs

theorem abs_le_l1Dist (t z : ι → ℝ) (i : ι) : |z i - t i| ≤ l1Dist t z := by
  unfold l1Dist
  exact Finset.single_le_sum (f := fun j => |z j - t j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- The sup metric is dominated by the ℓ¹ distance. -/
theorem dist_le_l1Dist (t z : ι → ℝ) : dist z t ≤ l1Dist t z := by
  refine (dist_pi_le_iff (l1Dist_nonneg t z)).mpr fun i => ?_
  rw [Real.dist_eq]
  exact abs_le_l1Dist t z i

/-- Attainment of the ℓ¹ distance to a closed nonempty set: intersect with a
closed ball to reduce to a compact set. -/
theorem exists_l1_min {S : Set (ι → ℝ)} (hS : IsClosed S) (hne : S.Nonempty)
    (t : ι → ℝ) : ∃ z ∈ S, ∀ w ∈ S, l1Dist t z ≤ l1Dist t w := by
  obtain ⟨z₀, hz₀⟩ := hne
  set R := l1Dist t z₀ with hR
  have hz₀K : z₀ ∈ S ∩ closedBall t R :=
    ⟨hz₀, by rw [mem_closedBall]; exact dist_le_l1Dist t z₀⟩
  obtain ⟨z, hzK, hz⟩ := ((isCompact_closedBall t R).inter_left hS).exists_isMinOn
    ⟨z₀, hz₀K⟩ (continuous_l1Dist t).continuousOn
  refine ⟨z, hzK.1, fun w hw => ?_⟩
  by_cases hwK : w ∈ closedBall t R
  · exact hz ⟨hw, hwK⟩
  · have h1 : l1Dist t z ≤ R := hz hz₀K
    have h2 : R < dist w t := by
      have := (not_iff_not.mpr mem_closedBall).mp hwK
      exact lt_of_not_ge this
    have h3 : dist w t ≤ l1Dist t w := dist_le_l1Dist t w
    linarith

/-! ## The transfer strictly decreases the ℓ¹ distance -/

/-- Scalar transfer bound: moving from `a` by `a⁺ - d` with `0 ≤ d ≤ a⁻`
lands within `|a| - a⁺` of the origin. -/
theorem abs_transfer (a d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ a⁻) :
    |a - (a⁺ - d)| ≤ |a| - a⁺ := by
  have hsub : a⁺ - a⁻ = a := posPart_sub_negPart a
  have hadd : a⁺ + a⁻ = |a| := posPart_add_negPart a
  have h1 : a - (a⁺ - d) = d - a⁻ := by linarith
  rw [h1, abs_of_nonpos (by linarith : d - a⁻ ≤ 0)]
  linarith

/-- Moving `q'` toward `q` by the extreme admissible transfer
`(q - q')⁺ - δ₂` decreases the ℓ¹ distance to `q` by at least
`∑ i, (q - q')⁺ i`. -/
theorem l1Dist_transfer_le (q q' δ₂ : ι → ℝ) (hδ₂ : δ₂ ∈ Icc 0 ((q - q')⁻)) :
    l1Dist q (q' + ((q - q')⁺ - δ₂)) ≤ l1Dist q q' - ∑ i, (q - q')⁺ i := by
  unfold l1Dist
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb := abs_transfer ((q - q') i) (δ₂ i) (hδ₂.1 i) (hδ₂.2 i)
  have h2 : |(q - q') i| = |q' i - q i| := by
    rw [Pi.sub_apply, abs_sub_comm]
  have hkey : (q' + ((q - q')⁺ - δ₂)) i - q i
      = -((q - q') i - (((q - q') i)⁺ - δ₂ i)) := by
    simp only [Pi.add_apply, Pi.sub_apply, posPart_apply]
    ring
  rw [hkey, abs_neg]
  show _ ≤ |q' i - q i| - ((q - q') i)⁺
  linarith

/-- Symmetric version: moving `q` toward `q'` by the same transfer decreases
the ℓ¹ distance to `q'` by at least `∑ i, (q - q')⁺ i`. -/
theorem l1Dist_transfer_le' (q q' δ₂ : ι → ℝ) (hδ₂ : δ₂ ∈ Icc 0 ((q - q')⁻)) :
    l1Dist q' (q - ((q - q')⁺ - δ₂)) ≤ l1Dist q' q - ∑ i, (q - q')⁺ i := by
  unfold l1Dist
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb := abs_transfer ((q - q') i) (δ₂ i) (hδ₂.1 i) (hδ₂.2 i)
  have h2 : |(q - q') i| = |q i - q' i| := by rw [Pi.sub_apply]
  have hkey : (q - ((q - q')⁺ - δ₂)) i - q' i
      = (q - q') i - (((q - q') i)⁺ - δ₂ i) := by
    simp only [Pi.sub_apply, posPart_apply]
    ring
  rw [hkey]
  show _ ≤ |q i - q' i| - ((q - q') i)⁺
  linarith

/-- From ℓ¹-optimality plus the availability of the extreme transfer, extract
the coordinatewise comparison `q ≤ q'`. -/
theorem le_of_l1_optimal {q q' : ι → ℝ}
    (h : l1Dist q q' - ∑ i, (q - q')⁺ i ≥ l1Dist q q' ∨
         l1Dist q' q - ∑ i, (q - q')⁺ i ≥ l1Dist q' q) : q ≤ q' := by
  have hsum : ∑ i, (q - q')⁺ i ≤ 0 := by rcases h with h | h <;> linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => show (0:ℝ) ≤ (q - q')⁺ i from posPart_nonneg ((q - q') i))).mp
    (le_antisymm hsum (Finset.sum_nonneg fun i _ =>
      show (0:ℝ) ≤ (q - q')⁺ i from posPart_nonneg ((q - q') i)))
  intro i
  have hi : ((q - q') i)⁺ = 0 := hzero i (Finset.mem_univ i)
  have := posPart_eq_zero.mp hi
  simpa [Pi.sub_apply, sub_nonpos] using this

/-! ## Proposition 2 -/

/-- **GHS Proposition 2** (`prop:qorderimplieswso`): the Q-order implies the
weak set order, for closed nonempty sets. -/
theorem qOrderSet_weakSetOrder {Q Q' : Set (ι → ℝ)} (h : QOrderSet Q Q')
    (hQ : IsClosed Q) (hQ' : IsClosed Q') (hne : Q.Nonempty) (hne' : Q'.Nonempty) :
    WeakSetOrder Q Q' := by
  constructor
  · -- for q ∈ Q, the ℓ¹-nearest q' ∈ Q' satisfies q ≤ q'
    intro q hq
    obtain ⟨q', hq', hmin⟩ := exists_l1_min hQ' hne' q
    refine ⟨q', hq', ?_⟩
    obtain ⟨δ₂, hδ₂, _, hmem'⟩ :=
      h q hq q' hq' ((q - q')⁺) ⟨posPart_nonneg _, le_refl _⟩
    have hopt := hmin _ hmem'
    have hbound := l1Dist_transfer_le q q' δ₂ hδ₂
    exact le_of_l1_optimal (Or.inl (by linarith))
  · -- for q' ∈ Q', the ℓ¹-nearest q ∈ Q satisfies q ≤ q'
    intro q' hq'
    obtain ⟨q, hq, hmin⟩ := exists_l1_min hQ hne q'
    refine ⟨q, hq, ?_⟩
    obtain ⟨δ₂, hδ₂, hmem, _⟩ :=
      h q hq q' hq' ((q - q')⁺) ⟨posPart_nonneg _, le_refl _⟩
    have hopt := hmin _ hmem
    have hbound := l1Dist_transfer_le' q q' δ₂ hδ₂
    exact le_of_l1_optimal (Or.inr (by linarith))

end GHS
