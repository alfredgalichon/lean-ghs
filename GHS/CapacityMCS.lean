import GHS.Topkis
import GHS.WeakSetOrder
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# GHS Phase 5: capacity-induced comparative statics (Theorem 2, item (4) at fixed `p`)

The "moreover" clause of Claim 2 / the `p = p'` case of Theorem 2(4), which is
what the deferred-acceptance algorithm consumes: if the cost `c` is
exchangeable, then the rejected sets
`r(p, qb) = argmin_{u ≥ 0} { c(qb - u) + ⟨p, u⟩ }`
are Q-ordered as the capacity `qb` increases.

* `qOrder_capacity` — exchangeability of `c` transfers to the penalized
  capacity objectives: the exchange for the pair `(qb' - u', qb - u)` is
  admissible for the pair `(u, u')` (box comparisons from
  `GHS/BoxCalculus.lean`), the linear part cancels exactly (`p = p'`), and
  the positivity constraint `u ≥ 0` is preserved by the transfer
  (`transfer_nonneg`).
* `qOrderSet_capacity` — the argmin sets are Q-ordered, by `dual_topkis`.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set

namespace GHS

variable {ι : Type*}

/-- The transfer preserves nonnegativity: if `u, u' ≥ 0`,
`δ₁ ∈ [0, (u-u')⁺]` and `δ₂ ∈ [0, (u-u')⁻]`, then `u - (δ₁ - δ₂) ≥ 0` and
`u' + (δ₁ - δ₂) ≥ 0`. -/
theorem transfer_nonneg {u u' δ₁ δ₂ : ι → ℝ} (hu : 0 ≤ u) (hu' : 0 ≤ u')
    (hδ₁ : δ₁ ∈ Icc 0 ((u - u')⁺)) (hδ₂ : δ₂ ∈ Icc 0 ((u - u')⁻)) :
    0 ≤ u - (δ₁ - δ₂) ∧ 0 ≤ u' + (δ₁ - δ₂) := by
  constructor <;> intro i
  · have h1 : δ₁ i ≤ (u i - u' i)⁺ := hδ₁.2 i
    have h2 : (0:ℝ) ≤ δ₂ i := hδ₂.1 i
    have h3 : (0:ℝ) ≤ u i := hu i
    have h4 : (0:ℝ) ≤ u' i := hu' i
    show (0:ℝ) ≤ u i - (δ₁ i - δ₂ i)
    rcases le_total (u i - u' i) 0 with h | h
    · rw [posPart_eq_zero.mpr h] at h1
      linarith
    · rw [posPart_eq_self.mpr h] at h1
      linarith
  · have h1 : (0:ℝ) ≤ δ₁ i := hδ₁.1 i
    have h2 : δ₂ i ≤ (u i - u' i)⁻ := hδ₂.2 i
    have h3 : (0:ℝ) ≤ u i := hu i
    have h4 : (0:ℝ) ≤ u' i := hu' i
    show (0:ℝ) ≤ u' i + (δ₁ i - δ₂ i)
    rcases le_total 0 (u i - u' i) with h | h
    · rw [negPart_eq_zero.mpr h] at h2
      linarith
    · have h5 : (u i - u' i)⁻ = -(u i - u' i) := by
        have := posPart_sub_negPart (u i - u' i)
        have h6 := posPart_eq_zero.mpr h
        linarith
      rw [h5] at h2
      linarith

/-- **Capacity Q-order (Theorem 2(4) at `p = p'`, penalized form).** If `c` is
exchangeable and `qb ≤ qb'`, the two capacity objectives (with the positivity
constraint folded in) are Q-ordered. -/
theorem qOrder_capacity [Fintype ι] {c : (ι → ℝ) → ERealTop}
    (hc : Exchangeable c) (p : ι → ℝ) {qb qb' : ι → ℝ} (hq : qb ≤ qb') :
    QOrder
      (fun u => (c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop)) + ind {v : ι → ℝ | 0 ≤ v} u)
      (fun u => (c (qb' - u) + ((p ⬝ᵥ u : ℝ) : ERealTop)) + ind {v : ι → ℝ | 0 ≤ v} u) := by
  intro u u' δ₁ hδ₁
  by_cases hu : (0 : ι → ℝ) ≤ u
  · by_cases hu' : (0 : ι → ℝ) ≤ u'
    · -- the interesting case: apply exchangeability to (qb' - u', qb - u)
      have hcomp : u - u' ≤ (qb' - u') - (qb - u) := by
        intro i
        have := hq i
        show u i - u' i ≤ (qb' i - u' i) - (qb i - u i)
        linarith
      have hδ₁' : δ₁ ∈ Icc 0 (((qb' - u') - (qb - u))⁺) :=
        Icc_posPart_subset hcomp hδ₁
      obtain ⟨δ₂, hδ₂', hkey⟩ := hc (qb' - u') (qb - u) δ₁ hδ₁'
      have hδ₂ : δ₂ ∈ Icc 0 ((u - u')⁻) :=
        ⟨hδ₂'.1, le_trans hδ₂'.2 (negPart_le_of_le hcomp)⟩
      refine ⟨δ₂, hδ₂, ?_⟩
      obtain ⟨hpos1, hpos2⟩ := transfer_nonneg hu hu' hδ₁ hδ₂
      have hm1 : u ∈ {v : ι → ℝ | 0 ≤ v} := hu
      have hm2 : u' ∈ {v : ι → ℝ | 0 ≤ v} := hu'
      have hm3 : u - (δ₁ - δ₂) ∈ {v : ι → ℝ | 0 ≤ v} := hpos1
      have hm4 : u' + (δ₁ - δ₂) ∈ {v : ι → ℝ | 0 ≤ v} := hpos2
      simp only [ind_of_mem hm1, ind_of_mem hm2, ind_of_mem hm3, ind_of_mem hm4,
        add_zero]
      -- arguments of c line up with the exchange output
      have harg1 : qb - (u - (δ₁ - δ₂)) = (qb - u) + (δ₁ - δ₂) := by abel
      have harg2 : qb' - (u' + (δ₁ - δ₂)) = (qb' - u') - (δ₁ - δ₂) := by abel
      rw [harg1, harg2]
      -- the linear parts cancel exactly
      have hlin : (p ⬝ᵥ (u - (δ₁ - δ₂)) : ℝ) + (p ⬝ᵥ (u' + (δ₁ - δ₂)) : ℝ)
          = (p ⬝ᵥ u : ℝ) + (p ⬝ᵥ u' : ℝ) := by
        rw [dotProduct_sub, dotProduct_add]
        ring
      -- assemble in `WithTop ℝ`
      calc c ((qb - u) + (δ₁ - δ₂)) + ↑(p ⬝ᵥ (u - (δ₁ - δ₂)))
            + (c ((qb' - u') - (δ₁ - δ₂)) + ↑(p ⬝ᵥ (u' + (δ₁ - δ₂))))
          = (c ((qb' - u') - (δ₁ - δ₂)) + c ((qb - u) + (δ₁ - δ₂)))
            + (↑(p ⬝ᵥ (u - (δ₁ - δ₂))) + ↑(p ⬝ᵥ (u' + (δ₁ - δ₂)))) := by
            abel
        _ ≤ (c (qb' - u') + c (qb - u))
            + (↑(p ⬝ᵥ (u - (δ₁ - δ₂))) + ↑(p ⬝ᵥ (u' + (δ₁ - δ₂)))) := by
            refine add_le_add ?_ (le_refl _)
            exact hkey
        _ = (c (qb - u) + ↑(p ⬝ᵥ u)) + (c (qb' - u') + ↑(p ⬝ᵥ u')) := by
            rw [← WithTop.coe_add, hlin, WithTop.coe_add]
            abel
    · refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
      have hm : u' ∉ {v : ι → ℝ | 0 ≤ v} := hu'
      simp only [ind_of_not_mem hm, add_top]
      exact le_top
  · refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
    have hm : u ∉ {v : ι → ℝ | 0 ≤ v} := hu
    simp only [ind_of_not_mem hm, add_top]
    exact le_top

/-- **Capacity-induced response (Theorem 2(4) at `p = p'` / Claim 2,
"moreover").** If `c` is exchangeable and the two capacity problems have
finite value somewhere on `{u ≥ 0}`, then the rejected sets
`r(p, qb) = argmin_{u ≥ 0} { c(qb - u) + ⟨p, u⟩ }` are Q-ordered:
`r(p, qb) ≤_Q r(p, qb')` for `qb ≤ qb'`. -/
theorem qOrderSet_capacity [Fintype ι] {c : (ι → ℝ) → ERealTop}
    (hc : Exchangeable c) (p : ι → ℝ) {qb qb' : ι → ℝ} (hq : qb ≤ qb')
    (hprop : ∃ u ∈ {v : ι → ℝ | 0 ≤ v}, c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤)
    (hprop' : ∃ u ∈ {v : ι → ℝ | 0 ≤ v}, c (qb' - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤) :
    QOrderSet
      (argminOn (fun u => c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop)) {v : ι → ℝ | 0 ≤ v})
      (argminOn (fun u => c (qb' - u) + ((p ⬝ᵥ u : ℝ) : ERealTop)) {v : ι → ℝ | 0 ≤ v}) :=
  dual_topkis (qOrder_capacity hc p hq) hprop hprop'

/-- **The step the deferred-acceptance well-definedness (Proposition 3)
consumes**: when the capacity shrinks from `qb'` to `qb ≤ qb'`, every old
rejection vector dominates some new rejection vector — via the weak set order
(Proposition 2) applied to the capacity Q-order. Hypotheses: the two rejected
sets are closed and nonempty (attainment). -/
theorem exists_rejection_le_of_capacity_le [Fintype ι] {c : (ι → ℝ) → ERealTop}
    (hc : Exchangeable c) (p : ι → ℝ) {qb qb' : ι → ℝ} (hq : qb ≤ qb')
    (hprop : ∃ u ∈ {v : ι → ℝ | 0 ≤ v}, c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤)
    (hprop' : ∃ u ∈ {v : ι → ℝ | 0 ≤ v}, c (qb' - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤)
    (hcl : IsClosed
      (argminOn (fun u => c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop)) {v : ι → ℝ | 0 ≤ v}))
    (hcl' : IsClosed
      (argminOn (fun u => c (qb' - u) + ((p ⬝ᵥ u : ℝ) : ERealTop)) {v : ι → ℝ | 0 ≤ v}))
    (hne : (argminOn (fun u => c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop))
      {v : ι → ℝ | 0 ≤ v}).Nonempty)
    (hne' : (argminOn (fun u => c (qb' - u) + ((p ⬝ᵥ u : ℝ) : ERealTop))
      {v : ι → ℝ | 0 ≤ v}).Nonempty) :
    ∀ r' ∈ argminOn (fun u => c (qb' - u) + ((p ⬝ᵥ u : ℝ) : ERealTop))
      {v : ι → ℝ | 0 ≤ v},
      ∃ r ∈ argminOn (fun u => c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop))
        {v : ι → ℝ | 0 ≤ v}, r ≤ r' :=
  (qOrderSet_weakSetOrder (qOrderSet_capacity hc p hq hprop hprop')
    hcl hcl' hne hne').2

end GHS
