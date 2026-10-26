import GHS.ExtendedDomainMCS
import GHS.PriceMCS
import GHS.WeakSetOrder

/-! # Relative-subgradient rejection order -/

open Set

namespace GHS

variable {n : ℕ}

local notation "V" => Fin n → ℝ

/-- Rejections written directly in terms of the relative subdifferential. -/
def relativeSubdiffRejections (D : Set V) (f : V → ℝ) (p qb : V) : Set V :=
  {u | 0 ≤ u ∧ Correspondence.SubgradOn D f p (qb - u)}

/-- Coordinate restriction to an arbitrary set of coordinates. -/
def coordinateProjection (D : Set (Fin n)) (x : V) : D → ℝ := fun i => x i.1

/-- The image of a set of vectors under coordinate restriction. -/
def projectedSet (D : Set (Fin n)) (X : Set V) : Set (D → ℝ) :=
  coordinateProjection D '' X

/-- Projected Q-order gives the one-sided coordinate comparison used in the
converse proof. -/
theorem projectedQOrder_exists_ge_on {D : Set (Fin n)} {X Y : Set V}
    (hQ : QOrderSet (projectedSet D X) (projectedSet D Y))
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∀ x ∈ X, ∃ y ∈ Y, ∀ i ∈ D, x i ≤ y i := by
  have hprojX : (projectedSet D X).Nonempty := by
    obtain ⟨x, hx⟩ := hX
    exact ⟨coordinateProjection D x, ⟨x, hx, rfl⟩⟩
  have hprojY : (projectedSet D Y).Nonempty := by
    obtain ⟨y, hy⟩ := hY
    exact ⟨coordinateProjection D y, ⟨y, hy, rfl⟩⟩
  have hw := qOrderSet_weakSetOrder_of_nonempty hQ hprojX hprojY
  intro x hx
  obtain ⟨yD, ⟨y, hy, hyD⟩, hxy⟩ := hw.1 (coordinateProjection D x) ⟨x, hx, rfl⟩
  subst yD
  exact ⟨y, hy, fun i hi => hxy ⟨i, hi⟩⟩

/-- A `D`-restricted Q-order gives the one-sided weak comparison used below. -/
theorem qOrderSetD_exists_ge_on_domain {D : Set (Fin n)} {X Y : Set V}
    (hQ : QOrderSetD D X Y) (hY : Y.Nonempty) :
    ∀ x ∈ X, ∃ y ∈ Y, ∀ i ∈ D, x i ≤ y i := by
  intro x hx
  obtain ⟨y, hy⟩ := hY
  classical
  let δ₁ : V := fun i => if i ∈ D then (x - y)⁺ i else 0
  have hδ₁ : δ₁ ∈ Icc 0 ((x - y)⁺) := by
    constructor <;> intro i
    · dsimp [δ₁]
      split
      · exact posPart_nonneg _
      · exact le_rfl
    · dsimp [δ₁]
      split
      · exact le_rfl
      · exact posPart_nonneg _
  have hδ₁D : ∀ i ∉ D, δ₁ i = 0 := by
    intro i hi
    simp [δ₁, hi]
  obtain ⟨δ₂, hδ₂, -, hy'⟩ := hQ x hx y hy δ₁ hδ₁ hδ₁D
  refine ⟨y + δ₁ - δ₂, hy', fun i hi => ?_⟩
  have hδ₂i := (hδ₂ i hi).2
  change δ₂ i ≤ (x i - y i)⁻ at hδ₂i
  have hsplit := posPart_sub_negPart (x i - y i)
  have hδ₁i : δ₁ i = (x - y)⁺ i := by simp [δ₁, hi]
  simp only [Pi.add_apply, Pi.sub_apply, hδ₁i, posPart_apply]
  linarith

/-- If the relative-subgradient rejection sets have the paper's projected
Q-monotonicity, then the weak Kelso--Crawford pair condition follows. -/
theorem KCpairOn_of_relativeSubdiffRejection_order {D P : Set V} {f : V → ℝ}
    (hne : ∀ p ∈ P, ∃ s, Correspondence.SubgradOn D f p s)
    (hR : ∀ p ∈ P, ∀ p' ∈ P, p ≤ p' → ∀ qb,
      QOrderSetD {i | p i = p' i}
        (relativeSubdiffRejections D f p qb)
        (relativeSubdiffRejections D f p' qb)) :
    Correspondence.KCpairOn D P f := by
  intro p hp p' hp' hpp'
  obtain ⟨σ, hσ⟩ := hne p hp
  obtain ⟨τ₀, hτ₀⟩ := hne p' hp'
  let qb : V := σ ⊔ τ₀
  have hσqb : σ ≤ qb := le_sup_left
  have hτ₀qb : τ₀ ≤ qb := le_sup_right
  have hσR : qb - σ ∈ relativeSubdiffRejections D f p qb := by
    refine ⟨fun i => sub_nonneg.mpr (hσqb i), ?_⟩
    simpa only [sub_sub_cancel] using hσ
  have hτ₀R : qb - τ₀ ∈ relativeSubdiffRejections D f p' qb := by
    refine ⟨fun i => sub_nonneg.mpr (hτ₀qb i), ?_⟩
    simpa only [sub_sub_cancel] using hτ₀
  obtain ⟨u', hu'R, hdom⟩ := qOrderSetD_exists_ge_on_domain
    (hR p hp p' hp' hpp' qb) ⟨qb - τ₀, hτ₀R⟩ (qb - σ) hσR
  refine ⟨σ, qb - u', hσ, hu'R.2, ?_⟩
  intro i hi
  have hui := hdom i hi
  change qb i - σ i ≤ u' i at hui
  change qb i - u' i ≤ σ i
  linarith

end GHS
