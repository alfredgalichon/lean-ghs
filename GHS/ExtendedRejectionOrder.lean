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

/-- The `D`-restricted Q-order used internally by the comparative-statics
proof implies the ordinary Q-order between the corresponding coordinate
projections, exactly as stated in the paper. -/
theorem qOrderSet_projected_of_qOrderSetD {D : Set (Fin n)} {X Y : Set V}
    (hQ : QOrderSetD D X Y) :
    QOrderSet (projectedSet D X) (projectedSet D Y) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ δ₁D hδ₁D
  classical
  let δ₁ : V := fun i => if hi : i ∈ D then δ₁D ⟨i, hi⟩ else 0
  have hδ₁ : δ₁ ∈ Icc 0 ((x - y)⁺) := by
    constructor <;> intro i
    · by_cases hi : i ∈ D
      · simpa [δ₁, hi] using hδ₁D.1 ⟨i, hi⟩
      · simp [δ₁, hi]
    · by_cases hi : i ∈ D
      · simpa [δ₁, hi, coordinateProjection, Pi.sub_apply, posPart_apply] using
          hδ₁D.2 ⟨i, hi⟩
      · simp [δ₁, hi, posPart_nonneg]
  have hδ₁support : ∀ i ∉ D, δ₁ i = 0 := by
    intro i hi
    simp [δ₁, hi]
  obtain ⟨δ₂, hδ₂, hx', hy'⟩ := hQ x hx y hy δ₁ hδ₁ hδ₁support
  let δ₂D : D → ℝ := fun i => δ₂ i.1
  have hδ₂D : δ₂D ∈ Icc 0
      ((coordinateProjection D x - coordinateProjection D y)⁻) := by
    constructor <;> intro i
    · exact (hδ₂ i.1 i.2).1
    · simpa [δ₂D, coordinateProjection, Pi.sub_apply, negPart_apply] using
        (hδ₂ i.1 i.2).2
  refine ⟨δ₂D, hδ₂D, ?_, ?_⟩
  · refine ⟨x - δ₁ + δ₂, hx', ?_⟩
    ext i
    simp [coordinateProjection, δ₁, δ₂D, i.2]
    ring
  · refine ⟨y + δ₁ - δ₂, hy', ?_⟩
    ext i
    simp [coordinateProjection, δ₁, δ₂D, i.2]
    ring

/-- The paper's exact forward comparative-statics statement. The existence of
a finite-cost `q ≤ qb` supplies finite feasible points for both constrained
problems, and the conclusion is the ordinary Q-order between the projected
rejection sets. -/
theorem qOrderSet_projected_capacity {c : V → ERealTop}
    (hc : Exchangeable c) {p p' qb qb' : V} (hp : p ≤ p') (hqb : qb ≤ qb')
    (hfeas : ∃ q, q ≤ qb ∧ c q ≠ ⊤) :
    QOrderSet
      (projectedSet {i | p i = p' i}
        (argminOn (fun u => c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop))
          {u : V | 0 ≤ u}))
      (projectedSet {i | p i = p' i}
        (argminOn (fun u => c (qb' - u) + ((p' ⬝ᵥ u : ℝ) : ERealTop))
          {u : V | 0 ≤ u})) := by
  obtain ⟨q, hqqb, hcq⟩ := hfeas
  let u : V := qb - q
  let u' : V := qb' - q
  have hu0 : 0 ≤ u := by
    intro i
    dsimp [u]
    linarith [hqqb i]
  have hu'0 : 0 ≤ u' := by
    intro i
    dsimp [u']
    linarith [hqqb i, hqb i]
  have hproper : ∃ u ∈ {v : V | 0 ≤ v},
      c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤ := by
    refine ⟨u, hu0, ?_⟩
    have harg : qb - u = q := by simp [u]
    rw [harg]
    exact WithTop.add_ne_top.mpr ⟨hcq, WithTop.coe_ne_top⟩
  have hproper' : ∃ u ∈ {v : V | 0 ≤ v},
      c (qb' - u) + ((p' ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤ := by
    refine ⟨u', hu'0, ?_⟩
    have harg : qb' - u' = q := by simp [u']
    rw [harg]
    exact WithTop.add_ne_top.mpr ⟨hcq, WithTop.coe_ne_top⟩
  exact qOrderSet_projected_of_qOrderSetD
    (qOrderSetD_capacity hc hp hqb hproper hproper')

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
