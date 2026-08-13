import GHS.CapacityMCS

/-!
# GHS Theorem 2, item (4) in full: joint price- and capacity-induced MCS

The `D`-restricted (projected) form of the capacity comparative statics,
completing Theorem 2(4): for `(p, q̄) ≤ (p', q̄')` the rejected sets are
Q-ordered **along the coincidence set** `D = {i : p i = p' i}`.  This is
the form the paper states via projections `Π_D`; here the projection is
carried by the `D`-restricted orders of `GHS/Orders.lean` (`δ₁` supported
on `D`, `δ₂` box-constrained only on `D`), which agree with the projected
orders on indicator functions (the paper's remark after the `(ε,D)`
definitions).

* `QOrderSetD` — the `D`-Q-order on sets (the specialization of `QOrderD`
  to indicators);
* `dual_topkisD` — the `D`-restricted dual Topkis theorem.  The paper uses
  this variant silently (erratum G10: the introduction's dual Topkis is
  proved only for the plain Q-order); here it is stated and proved;
* `qOrderD_capacity` — the joint penalized comparison: exchangeability of
  `c` transfers to the objectives `u ↦ c(q̄-u) + ⟨p,u⟩ + ι_{u≥0}` along
  `(p, q̄) ≤ (p', q̄')`, with `δ₁` supported on `{p = p'}`.  Relative to the
  fixed-`p` case (`GHS/CapacityMCS.lean`), the linear parts no longer
  cancel: they contribute `(p'-p)ᵀδ₁ - (p'-p)ᵀδ₂`, where the first term
  vanishes because `δ₁` lives on the coincidence set and the second is
  nonnegative because `p ≤ p'` and `δ₂ ≥ 0` — the paper's one-line
  computation, made precise;
* `qOrderSetD_capacity` — **Theorem 2(4)**, in the `D`-restricted set
  order.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set

namespace GHS

variable {ι : Type*}

/-- The `D`-Q-order on sets: the specialization of `QOrderD` to indicator
functions.  `δ₁` is supported on `D` and box-constrained; `δ₂` is
box-constrained only on `D`. -/
def QOrderSetD (D : Set ι) (X Y : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ δ₁ ∈ Icc 0 ((x - y)⁺), (∀ i ∉ D, δ₁ i = 0) →
    ∃ δ₂ : ι → ℝ, (∀ i ∈ D, δ₂ i ∈ Icc 0 ((x - y)⁻ i)) ∧
      x - δ₁ + δ₂ ∈ X ∧ y + δ₁ - δ₂ ∈ Y

/-- **`D`-restricted dual Topkis** (the variant the paper's proof of
(1)⇒(4) uses silently — erratum G10): if the penalized objectives are
`D`-Q-ordered, so are their argmin sets. -/
theorem dual_topkisD {D : Set ι} {ψ ψ' : (ι → ℝ) → ERealTop}
    {Q Q' : Set (ι → ℝ)}
    (h : QOrderD D (fun q => ψ q + ind Q q) (fun q => ψ' q + ind Q' q))
    (hprop : ∃ q ∈ Q, ψ q ≠ ⊤) (hprop' : ∃ q' ∈ Q', ψ' q' ≠ ⊤) :
    QOrderSetD D (argminOn ψ Q) (argminOn ψ' Q') := by
  rintro q ⟨hqQ, hqmin⟩ q' ⟨hq'Q', hq'min⟩ δ₁ hδ₁ hδ₁D
  obtain ⟨q₀, hq₀, hfin₀⟩ := hprop
  obtain ⟨q₁, hq₁, hfin₁⟩ := hprop'
  have hψq : ψ q ≠ ⊤ := ne_top_of_le_ne_top hfin₀ (hqmin q₀ hq₀)
  have hψ'q' : ψ' q' ≠ ⊤ := ne_top_of_le_ne_top hfin₁ (hq'min q₁ hq₁)
  obtain ⟨δ₂, hδ₂, hkey⟩ := h q q' δ₁ hδ₁ hδ₁D
  simp only [ind_of_mem hqQ, ind_of_mem hq'Q', add_zero] at hkey
  have hne := ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hψq, hψ'q'⟩) hkey
  obtain ⟨hne1, hne2⟩ := WithTop.add_ne_top.mp hne
  have hmem1 : q - δ₁ + δ₂ ∈ Q := by
    by_contra hmem
    rw [ind_of_not_mem hmem] at hne1
    simp at hne1
  have hmem2 : q' + δ₁ - δ₂ ∈ Q' := by
    by_contra hmem
    rw [ind_of_not_mem hmem] at hne2
    simp at hne2
  simp only [ind_of_mem hmem1, ind_of_mem hmem2, add_zero] at hkey
  obtain ⟨e1, e2⟩ := eq_of_le_of_le_of_add_le_add hψq hψ'q'
    (hqmin _ hmem1) (hq'min _ hmem2) hkey
  refine ⟨δ₂, hδ₂, ⟨hmem1, fun z hz => ?_⟩, ⟨hmem2, fun z hz => ?_⟩⟩
  · rw [e1]; exact hqmin z hz
  · rw [e2]; exact hq'min z hz

/-- **Joint capacity/price Q-order (Theorem 2(4), penalized form).** If `c`
is exchangeable and `(p, q̄) ≤ (p', q̄')`, the two capacity objectives are
`D`-Q-ordered along the coincidence set `D = {i : p i = p' i}`. -/
theorem qOrderD_capacity [Fintype ι] {c : (ι → ℝ) → ERealTop}
    (hc : Exchangeable c) {p p' qb qb' : ι → ℝ} (hp : p ≤ p') (hq : qb ≤ qb') :
    QOrderD {i | p i = p' i}
      (fun u => (c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop))
        + ind {v : ι → ℝ | 0 ≤ v} u)
      (fun u => (c (qb' - u) + ((p' ⬝ᵥ u : ℝ) : ERealTop))
        + ind {v : ι → ℝ | 0 ≤ v} u) := by
  intro u u' δ₁ hδ₁ hδ₁D
  by_cases hu : (0 : ι → ℝ) ≤ u
  · by_cases hu' : (0 : ι → ℝ) ≤ u'
    · -- apply exchangeability to the pair (qb' - u', qb - u)
      have hcomp : u - u' ≤ (qb' - u') - (qb - u) := by
        intro i
        have := hq i
        show u i - u' i ≤ (qb' i - u' i) - (qb i - u i)
        linarith
      have hδ₁' : δ₁ ∈ Icc 0 (((qb' - u') - (qb - u))⁺) :=
        Icc_posPart_subset hcomp hδ₁
      obtain ⟨δ₂, hδ₂', hkey⟩ := hc (qb' - u') (qb - u) δ₁ hδ₁'
      have hδ₂full : δ₂ ∈ Icc 0 ((u - u')⁻) :=
        ⟨hδ₂'.1, le_trans hδ₂'.2 (negPart_le_of_le hcomp)⟩
      refine ⟨δ₂, fun i _ => ⟨hδ₂full.1 i, hδ₂full.2 i⟩, ?_⟩
      obtain ⟨hpos1, hpos2⟩ := transfer_nonneg hu hu' hδ₁ hδ₂full
      have hm1 : u ∈ {v : ι → ℝ | 0 ≤ v} := hu
      have hm2 : u' ∈ {v : ι → ℝ | 0 ≤ v} := hu'
      have hm3 : u - δ₁ + δ₂ ∈ {v : ι → ℝ | 0 ≤ v} := by
        have he : u - δ₁ + δ₂ = u - (δ₁ - δ₂) := by abel
        rw [he]
        exact hpos1
      have hm4 : u' + δ₁ - δ₂ ∈ {v : ι → ℝ | 0 ≤ v} := by
        have he : u' + δ₁ - δ₂ = u' + (δ₁ - δ₂) := by abel
        rw [he]
        exact hpos2
      simp only [ind_of_mem hm1, ind_of_mem hm2, ind_of_mem hm3,
        ind_of_mem hm4, add_zero]
      -- arguments of c line up with the exchange output
      have harg1 : qb - (u - δ₁ + δ₂) = (qb - u) + (δ₁ - δ₂) := by abel
      have harg2 : qb' - (u' + δ₁ - δ₂) = (qb' - u') - (δ₁ - δ₂) := by abel
      rw [harg1, harg2]
      -- the linear parts: (p'-p)ᵀδ₁ = 0 on the coincidence set,
      -- (p'-p)ᵀδ₂ ≥ 0 since p ≤ p' and δ₂ ≥ 0
      have hlin : (p ⬝ᵥ (u - δ₁ + δ₂) : ℝ) + (p' ⬝ᵥ (u' + δ₁ - δ₂) : ℝ)
          ≤ (p ⬝ᵥ u : ℝ) + (p' ⬝ᵥ u' : ℝ) := by
        have h1 : (p' - p) ⬝ᵥ δ₁ = 0 := by
          simp only [dotProduct, Pi.sub_apply]
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : i ∈ {i | p i = p' i}
          · have : p i = p' i := hi
            rw [this]
            ring
          · rw [hδ₁D i hi, mul_zero]
        have h2 : 0 ≤ (p' - p) ⬝ᵥ δ₂ := by
          simp only [dotProduct, Pi.sub_apply]
          refine Finset.sum_nonneg fun i _ => ?_
          have ha : p i ≤ p' i := hp i
          have hb : (0:ℝ) ≤ δ₂ i := hδ₂full.1 i
          nlinarith
        have e1 : p ⬝ᵥ (u - δ₁ + δ₂) = p ⬝ᵥ u - p ⬝ᵥ δ₁ + p ⬝ᵥ δ₂ := by
          rw [dotProduct_add, dotProduct_sub]
        have e2 : p' ⬝ᵥ (u' + δ₁ - δ₂) = p' ⬝ᵥ u' + p' ⬝ᵥ δ₁ - p' ⬝ᵥ δ₂ := by
          rw [dotProduct_sub, dotProduct_add]
        have e3 : (p' - p) ⬝ᵥ δ₁ = p' ⬝ᵥ δ₁ - p ⬝ᵥ δ₁ := sub_dotProduct _ _ _
        have e4 : (p' - p) ⬝ᵥ δ₂ = p' ⬝ᵥ δ₂ - p ⬝ᵥ δ₂ := sub_dotProduct _ _ _
        linarith
      -- assemble in `WithTop ℝ`
      calc c ((qb - u) + (δ₁ - δ₂)) + ↑(p ⬝ᵥ (u - δ₁ + δ₂))
            + (c ((qb' - u') - (δ₁ - δ₂)) + ↑(p' ⬝ᵥ (u' + δ₁ - δ₂)))
          = (c ((qb' - u') - (δ₁ - δ₂)) + c ((qb - u) + (δ₁ - δ₂)))
            + ↑(p ⬝ᵥ (u - δ₁ + δ₂) + p' ⬝ᵥ (u' + δ₁ - δ₂)) := by
            rw [WithTop.coe_add]
            abel
        _ ≤ (c (qb' - u') + c (qb - u)) + ↑(p ⬝ᵥ u + p' ⬝ᵥ u') := by
            refine add_le_add hkey ?_
            exact WithTop.coe_le_coe.mpr hlin
        _ = (c (qb - u) + ↑(p ⬝ᵥ u)) + (c (qb' - u') + ↑(p' ⬝ᵥ u')) := by
            rw [WithTop.coe_add]
            abel
    · refine ⟨0, fun i _ => ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
      have hm : u' ∉ {v : ι → ℝ | 0 ≤ v} := hu'
      simp only [ind_of_not_mem hm, add_top]
      exact le_top
  · refine ⟨0, fun i _ => ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
    have hm : u ∉ {v : ι → ℝ | 0 ≤ v} := hu
    simp only [ind_of_not_mem hm, add_top]
    exact le_top

/-- **GHS Theorem 2, item (4), in full.** If `c` is exchangeable and
`(p, q̄) ≤ (p', q̄')`, the rejected sets
`r(p, q̄) = argmin_{u ≥ 0} { c(q̄ - u) + ⟨p, u⟩ }` are Q-ordered along the
coincidence set `{i : p i = p' i}` (the paper's projected order
`Π_{p=p'} r(p,q̄) ≤_Q Π_{p=p'} r(p',q̄')`, in `D`-restricted form). -/
theorem qOrderSetD_capacity [Fintype ι] {c : (ι → ℝ) → ERealTop}
    (hc : Exchangeable c) {p p' qb qb' : ι → ℝ} (hp : p ≤ p') (hq : qb ≤ qb')
    (hprop : ∃ u ∈ {v : ι → ℝ | 0 ≤ v},
      c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤)
    (hprop' : ∃ u ∈ {v : ι → ℝ | 0 ≤ v},
      c (qb' - u) + ((p' ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤) :
    QOrderSetD {i | p i = p' i}
      (argminOn (fun u => c (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop))
        {v : ι → ℝ | 0 ≤ v})
      (argminOn (fun u => c (qb' - u) + ((p' ⬝ᵥ u : ℝ) : ERealTop))
        {v : ι → ℝ | 0 ≤ v}) :=
  dual_topkisD (qOrderD_capacity hc hp hq) hprop hprop'

end GHS
