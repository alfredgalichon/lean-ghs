import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

/-!
# GHS Phase 0: the P- and Q-orders (vocabulary)

Definitions for Galichon–Hsieh–Sylvestre, *Monotone comparative statics for
submodular functions* (submitted version 2025-03-07):

* `GHS.QOrder`, `GHS.Exchangeable` — the Q-order on extended-real-valued
  functions (paper Definition "Q-order for functions and exchangeability",
  with the `(x-y)` vs `(q-q')` typo fixed, errata T2);
* `GHS.POrder`, `GHS.Submodular` — the P-order on functions;
* `GHS.QOrderSet`, `GHS.IsMatron` — the Q-order on sets, matrons
  (paper Definition `def:DdsoOnSets`);
* `GHS.POrderSet`, `GHS.IsSublattice` — Veinott's strong set order, sublattices;
* `GHS.QOrderED`, `GHS.POrderED` — the `(ε, D)`-refinements of Appendix A;
* `GHS.QOrderD`, `GHS.POrderD` — their `ε = 0`, non-strict variants.

Functions take values in `ℝ∞ := WithTop ℝ` (convex proper functions never take
`-∞`, and `⊤` gives indicator functions). A convenient consequence, recorded in
`qOrder_iff_ne_top` / `pOrder_iff_ne_top`: the paper's domain restrictions
("for `q ∈ dom ψ`, `q' ∈ dom ψ'`") are *automatic* for the non-strict orders,
because a `⊤` on the right-hand side trivializes the inequality. The strict
`(ε, D)`-orders do carry explicit domain hypotheses, as in the paper.

Statements are taken with the errata fixes
(`pq-convexity/papers/galichon-hsieh-sylvestre/errata.md`); in particular
nothing here depends on the erroneous Example 1 or on Claim 2(3).

Smoke tests at the end: singletons are matrons and sublattices, and the two
set orders reduce to the coordinatewise order on singletons (the paper's two
remarks after `def:DdsoOnSets`) — these validate the ∀/∃ structure of the
definitions.
-/

open Set

namespace GHS

variable {ι : Type*}

/-- Extended reals `ℝ ∪ {+∞}`, the value space for costs and indicators. -/
abbrev ERealTop : Type := WithTop ℝ

/-! ## Orders on functions -/

/-- The **Q-order** on functions (GHS eq. (2.11), "Exchangeability"):
`ψ ≤_Q ψ'` iff for all `q, q'` and every `δ₁ ∈ [0, (q-q')⁺]` there is
`δ₂ ∈ [0, (q-q')⁻]` with
`ψ (q - (δ₁ - δ₂)) + ψ' (q' + (δ₁ - δ₂)) ≤ ψ q + ψ' q'`.
Domain restrictions are omitted: they are automatic (`qOrder_iff_ne_top`). -/
def QOrder (ψ ψ' : (ι → ℝ) → ERealTop) : Prop :=
  ∀ q q' : ι → ℝ, ∀ δ₁ ∈ Icc 0 ((q - q')⁺), ∃ δ₂ ∈ Icc 0 ((q - q')⁻),
    ψ (q - (δ₁ - δ₂)) + ψ' (q' + (δ₁ - δ₂)) ≤ ψ q + ψ' q'

/-- A function is **exchangeable** when `ψ ≤_Q ψ`. -/
def Exchangeable (ψ : (ι → ℝ) → ERealTop) : Prop := QOrder ψ ψ

/-- The **P-order** on functions (GHS eq. (2.13)): `φ ≤_P φ'` iff
`φ (p ⊓ p') + φ' (p ⊔ p') ≤ φ p + φ' p'` for all `p, p'`.
Domain restrictions are again automatic. -/
def POrder (φ φ' : (ι → ℝ) → ERealTop) : Prop :=
  ∀ p p' : ι → ℝ, φ (p ⊓ p') + φ' (p ⊔ p') ≤ φ p + φ' p'

/-- A function is **submodular** when `φ ≤_P φ`. -/
def Submodular (φ : (ι → ℝ) → ERealTop) : Prop := POrder φ φ

/-! ## Orders on sets -/

/-- The **Q-order** on sets (GHS Definition `def:DdsoOnSets`): `X ≤_Q Y` iff for
`x ∈ X`, `y ∈ Y` and every `δ₁ ∈ [0, (x-y)⁺]` there is `δ₂ ∈ [0, (x-y)⁻]` with
`x - (δ₁ - δ₂) ∈ X` and `y + (δ₁ - δ₂) ∈ Y`. -/
def QOrderSet (X Y : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ δ₁ ∈ Icc 0 ((x - y)⁺), ∃ δ₂ ∈ Icc 0 ((x - y)⁻),
    x - (δ₁ - δ₂) ∈ X ∧ y + (δ₁ - δ₂) ∈ Y

/-- A **matron** is a set with `X ≤_Q X`. -/
def IsMatron (X : Set (ι → ℝ)) : Prop := QOrderSet X X

/-- The **P-order** (Veinott's strong set order): `X ≤_P Y` iff for all
`x ∈ X`, `y ∈ Y`, `x ⊓ y ∈ X` and `x ⊔ y ∈ Y`. -/
def POrderSet (X Y : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ⊓ y ∈ X ∧ x ⊔ y ∈ Y

/-- A **sublattice** is a set with `X ≤_P X`. -/
def IsSublattice (X : Set (ι → ℝ)) : Prop := POrderSet X X

/-! ## The `(ε, D)`-refinements (Appendix A)

`δ₁` is supported on `D` and box-constrained; `δ₂` is box-constrained *only on*
`D` (free off `D`). The inequality is strict with an `ε` slack, so the domain
hypotheses `f x ≠ ⊤`, `g y ≠ ⊤` are substantive here, matching the paper's
"for any `x` in the domain of `f`, `y` in the domain of `g`". -/

/-- The `(ε, D)`-Q-order `f ≤_{(ε,D),Q} g` (GHS Appendix A, first definition). -/
def QOrderED (ε : ℝ) (D : Set ι) (f g : (ι → ℝ) → ERealTop) : Prop :=
  ∀ x y : ι → ℝ, f x ≠ ⊤ → g y ≠ ⊤ →
    ∀ δ₁ ∈ Icc 0 ((x - y)⁺), (∀ i ∉ D, δ₁ i = 0) →
      ∃ δ₂ : ι → ℝ, (∀ i ∈ D, δ₂ i ∈ Icc 0 ((x - y)⁻ i)) ∧
        f (x - δ₁ + δ₂) + g (y + δ₁ - δ₂) < f x + g y + (ε : ERealTop)

/-- The `(ε, D)`-P-order `f ≤_{(ε,D),P} g` (GHS Appendix A, second definition):
for every `λ ∈ ℝ^ι` and `p_f, p_g` supported on `D`,
`g (λ + p_g ⊔ p_f) + f (λ + p_g ⊓ p_f) < g (λ + p_g) + f (λ + p_f) + ε`,
required when the right-hand side is finite. -/
def POrderED (ε : ℝ) (D : Set ι) (f g : (ι → ℝ) → ERealTop) : Prop :=
  ∀ lam pf pg : ι → ℝ, (∀ i ∉ D, pf i = 0) → (∀ i ∉ D, pg i = 0) →
    f (lam + pf) ≠ ⊤ → g (lam + pg) ≠ ⊤ →
      g (lam + pg ⊔ pf) + f (lam + pg ⊓ pf)
        < g (lam + pg) + f (lam + pf) + (ε : ERealTop)

/-- The `D`-Q-order (`ε = 0`, non-strict; GHS Appendix A, after the two
`(ε,D)` definitions). -/
def QOrderD (D : Set ι) (f g : (ι → ℝ) → ERealTop) : Prop :=
  ∀ x y : ι → ℝ, ∀ δ₁ ∈ Icc 0 ((x - y)⁺), (∀ i ∉ D, δ₁ i = 0) →
    ∃ δ₂ : ι → ℝ, (∀ i ∈ D, δ₂ i ∈ Icc 0 ((x - y)⁻ i)) ∧
      f (x - δ₁ + δ₂) + g (y + δ₁ - δ₂) ≤ f x + g y

/-- The `D`-P-order (`ε = 0`, non-strict). -/
def POrderD (D : Set ι) (f g : (ι → ℝ) → ERealTop) : Prop :=
  ∀ lam pf pg : ι → ℝ, (∀ i ∉ D, pf i = 0) → (∀ i ∉ D, pg i = 0) →
    g (lam + pg ⊔ pf) + f (lam + pg ⊓ pf) ≤ g (lam + pg) + f (lam + pf)

/-! ## Domain restrictions are automatic for the non-strict orders -/

/-- The Q-order need only be checked at points where both values are finite:
if `ψ q = ⊤` or `ψ' q' = ⊤` the right-hand side is `⊤` and `δ₂ = 0` works. -/
theorem qOrder_iff_ne_top {ψ ψ' : (ι → ℝ) → ERealTop} :
    QOrder ψ ψ' ↔
      ∀ q q' : ι → ℝ, ψ q ≠ ⊤ → ψ' q' ≠ ⊤ →
        ∀ δ₁ ∈ Icc 0 ((q - q')⁺), ∃ δ₂ ∈ Icc 0 ((q - q')⁻),
          ψ (q - (δ₁ - δ₂)) + ψ' (q' + (δ₁ - δ₂)) ≤ ψ q + ψ' q' := by
  constructor
  · intro h q q' _ _ δ₁ hδ₁
    exact h q q' δ₁ hδ₁
  · intro h q q' δ₁ hδ₁
    by_cases hq : ψ q = ⊤
    · refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
      simp [hq]
    by_cases hq' : ψ' q' = ⊤
    · refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
      simp [hq']
    exact h q q' hq hq' δ₁ hδ₁

/-- Same remark for the P-order. -/
theorem pOrder_iff_ne_top {φ φ' : (ι → ℝ) → ERealTop} :
    POrder φ φ' ↔
      ∀ p p' : ι → ℝ, φ p ≠ ⊤ → φ' p' ≠ ⊤ →
        φ (p ⊓ p') + φ' (p ⊔ p') ≤ φ p + φ' p' := by
  constructor
  · intro h p p' _ _
    exact h p p'
  · intro h p p'
    by_cases hp : φ p = ⊤
    · simp [hp]
    by_cases hp' : φ' p' = ⊤
    · simp [hp']
    exact h p p' hp hp'

/-! ## Smoke tests: singletons

The paper's two remarks after `def:DdsoOnSets`: on singletons, both set orders
reduce to the coordinatewise order. These validate the ∀/∃ structure of the
definitions before anything is built on them. -/

/-- On `ι → ℝ`, the positive part acts coordinatewise (definitional). -/
@[simp] lemma posPart_apply (f : ι → ℝ) (i : ι) : f⁺ i = (f i)⁺ := rfl

/-- On `ι → ℝ`, the negative part acts coordinatewise (definitional). -/
@[simp] lemma negPart_apply (f : ι → ℝ) (i : ι) : f⁻ i = (f i)⁻ := rfl

/-- In the Q-order, `{x} ≤_Q {y}` forces `δ₁ = δ₂`; since they have disjoint
supports both vanish, so the order holds iff `(x - y)⁺ = 0`, i.e. `x ≤ y`. -/
theorem qOrderSet_singleton_iff (x y : ι → ℝ) :
    QOrderSet {x} {y} ↔ x ≤ y := by
  constructor
  · intro h
    -- apply the order to the extreme perturbation δ₁ = (x - y)⁺
    obtain ⟨δ₂, hδ₂, hx, _⟩ :=
      h x rfl y rfl ((x - y)⁺) ⟨posPart_nonneg _, le_refl _⟩
    -- membership in the singleton forces δ₁ = δ₂
    have hxeq : x - ((x - y)⁺ - δ₂) = x := hx
    have hδ : (x - y)⁺ = δ₂ := sub_eq_zero.mp (sub_eq_self.mp hxeq)
    -- coordinatewise: (x-y)⁺ i ≤ (x-y)⁻ i, but the parts have disjoint
    -- supports, so (x-y)⁺ i = 0 for every i
    intro i
    have hle : ((x - y) i)⁺ ≤ ((x - y) i)⁻ := by
      have h2 : δ₂ i ≤ (x - y)⁻ i := hδ₂.2 i
      rw [← hδ] at h2
      simpa using h2
    by_contra hxy
    push_neg at hxy
    have hgt : 0 < (x - y) i := by
      have : y i < x i := hxy
      simpa [Pi.sub_apply, sub_pos] using this
    rw [posPart_eq_self.mpr hgt.le, negPart_eq_zero.mpr hgt.le] at hle
    exact absurd hle (not_le.mpr hgt)
  · intro hxy a ha b hb δ₁ hδ₁
    have ha' : a = x := ha
    have hb' : b = y := hb
    -- x ≤ y means (a - b)⁺ = 0, so δ₁ = 0 and δ₂ = 0 works
    have hpos : (a - b)⁺ = 0 := by
      funext i
      show ((a - b) i)⁺ = 0
      refine posPart_eq_zero.mpr ?_
      have hi : x i ≤ y i := hxy i
      simp [ha', hb', Pi.sub_apply, hi]
    have hδ₁0 : δ₁ = 0 := le_antisymm (hpos ▸ hδ₁.2) hδ₁.1
    refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_, ?_⟩
    · show a - (δ₁ - 0) ∈ ({x} : Set (ι → ℝ))
      simp [hδ₁0, ha']
    · show b + (δ₁ - 0) ∈ ({y} : Set (ι → ℝ))
      simp [hδ₁0, hb']

/-- In the P-order, `{x} ≤_P {y}` iff `x ≤ y`. -/
theorem pOrderSet_singleton_iff (x y : ι → ℝ) :
    POrderSet {x} {y} ↔ x ≤ y := by
  constructor
  · intro h
    obtain ⟨hmeet, _⟩ := h x rfl y rfl
    have : x ⊓ y = x := hmeet
    exact inf_eq_left.mp this
  · intro hxy x' hx' y' hy'
    subst hx'; subst hy'
    exact ⟨inf_eq_left.mpr hxy, sup_eq_right.mpr hxy⟩

/-- Every singleton is a matron. -/
theorem isMatron_singleton (x : ι → ℝ) : IsMatron {x} :=
  (qOrderSet_singleton_iff x x).mpr le_rfl

/-- Every singleton is a sublattice. -/
theorem isSublattice_singleton (x : ι → ℝ) : IsSublattice {x} :=
  (pOrderSet_singleton_iff x x).mpr le_rfl

end GHS
