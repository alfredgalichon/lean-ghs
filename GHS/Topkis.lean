import GHS.BoxCalculus

/-!
# GHS Phase 2: Topkis (Claim 3) and its dual (Theorem 1)

The two elementary monotone-comparative-statics theorems of GHS §2.3:

* `GHS.topkis` — **Claim 3 (Topkis)**: if `φ ≤_P φ'` and `P ≤_P P'` then
  `argmin_P φ ≤_P argmin_{P'} φ'`.
* `GHS.dual_topkis` — **Theorem 1 (Dual of Topkis)**: if
  `ψ + ι_Q ≤_Q ψ' + ι_{Q'}` then `argmin_Q ψ ≤_Q argmin_{Q'} ψ'`.
  The hypothesis packages the paper's itemized one (existence of `δ₂` keeping
  both perturbed points feasible while not increasing the total cost): a `⊤`
  from an indicator on the left forces infeasibility, so the single Q-order
  inequality on the penalized functions carries the membership requirements.

**Properness matters.** The paper states both results for *real-valued*
functions; in the extended-real setting they are false without properness
(e.g. `φ ≡ ⊤` makes the hypotheses vacuous but `argmin_P φ = P`). We assume
each function takes a finite value somewhere on its feasible set — this makes
every argmin value finite, which is what the "sum of two nonnegative gaps is
zero" step of the paper's proofs needs (`eq_of_le_of_le_of_add_le_add`).

Unconstrained corollaries (`P = univ`) are provided as `topkis_univ`,
`dual_topkis_univ`, and the bridge from the paper's itemized hypothesis as
`qOrder_add_ind_of_exchange`.
-/

open Set

namespace GHS

variable {ι : Type*}

/-! ## Convex indicators and argmin sets -/

open Classical in
/-- The convex indicator `ι_P`: `0` on `P`, `⊤` off `P`. -/
noncomputable def ind (P : Set (ι → ℝ)) : (ι → ℝ) → ERealTop :=
  fun p => if p ∈ P then 0 else ⊤

@[simp] theorem ind_of_mem {P : Set (ι → ℝ)} {p : ι → ℝ} (hp : p ∈ P) :
    ind P p = 0 := if_pos hp

@[simp] theorem ind_of_not_mem {P : Set (ι → ℝ)} {p : ι → ℝ} (hp : p ∉ P) :
    ind P p = ⊤ := if_neg hp

@[simp] theorem ind_univ (p : ι → ℝ) : ind (univ : Set (ι → ℝ)) p = 0 :=
  ind_of_mem (mem_univ p)

/-- The set of minimizers of `φ` over the feasible set `P`. -/
def argminOn (φ : (ι → ℝ) → ERealTop) (P : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {p | p ∈ P ∧ ∀ q ∈ P, φ p ≤ φ q}

theorem argminOn_univ (φ : (ι → ℝ) → ERealTop) :
    argminOn φ univ = {p | ∀ q, φ p ≤ φ q} := by
  ext p; simp [argminOn]

/-! ## The optimality-gap lemma -/

/-- If `c ≤ a`, `d ≤ b`, `a + b ≤ c + d` and `c, d` are finite, then `a = c`
and `b = d`.  This is the "both gaps vanish" step common to the Topkis and
dual-Topkis proofs; finiteness of the right-hand side is essential. -/
theorem eq_of_le_of_le_of_add_le_add {a b c d : ERealTop} (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (hca : c ≤ a) (hdb : d ≤ b) (h : a + b ≤ c + d) : a = c ∧ b = d := by
  have hcd : c + d ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hc, hd⟩
  have hab : a + b ≠ ⊤ := ne_top_of_le_ne_top hcd h
  obtain ⟨ha, hb⟩ := WithTop.add_ne_top.mp hab
  lift a to ℝ using ha
  lift b to ℝ using hb
  lift c to ℝ using hc
  lift d to ℝ using hd
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  rw [WithTop.coe_le_coe] at hca hdb
  constructor <;> · norm_cast; linarith

/-! ## Claim 3: Topkis -/

/-- **Topkis (GHS Claim 3).** If `φ ≤_P φ'`, `P ≤_P P'`, and each function is
finite somewhere on its feasible set, then the constrained argmins are ordered
in the strong set order: `argmin_P φ ≤_P argmin_{P'} φ'`. -/
theorem topkis {φ φ' : (ι → ℝ) → ERealTop} {P P' : Set (ι → ℝ)}
    (hfun : POrder φ φ') (hset : POrderSet P P')
    (hprop : ∃ p ∈ P, φ p ≠ ⊤) (hprop' : ∃ p ∈ P', φ' p ≠ ⊤) :
    POrderSet (argminOn φ P) (argminOn φ' P') := by
  rintro p ⟨hpP, hpmin⟩ p' ⟨hp'P', hp'min⟩
  obtain ⟨p₀, hp₀, hfin₀⟩ := hprop
  obtain ⟨p₁, hp₁, hfin₁⟩ := hprop'
  have hφp : φ p ≠ ⊤ := ne_top_of_le_ne_top hfin₀ (hpmin p₀ hp₀)
  have hφ'p' : φ' p' ≠ ⊤ := ne_top_of_le_ne_top hfin₁ (hp'min p₁ hp₁)
  obtain ⟨hmeetP, hjoinP'⟩ := hset p hpP p' hp'P'
  obtain ⟨e1, e2⟩ := eq_of_le_of_le_of_add_le_add hφp hφ'p'
    (hpmin _ hmeetP) (hp'min _ hjoinP') (hfun p p')
  refine ⟨⟨hmeetP, fun q hq => ?_⟩, ⟨hjoinP', fun q hq => ?_⟩⟩
  · rw [e1]; exact hpmin q hq
  · rw [e2]; exact hp'min q hq

/-- Unconstrained Topkis: `φ ≤_P φ'` orders the global argmins. -/
theorem topkis_univ {φ φ' : (ι → ℝ) → ERealTop}
    (hfun : POrder φ φ') (hprop : ∃ p, φ p ≠ ⊤) (hprop' : ∃ p, φ' p ≠ ⊤) :
    POrderSet (argminOn φ univ) (argminOn φ' univ) := by
  obtain ⟨p₀, h₀⟩ := hprop
  obtain ⟨p₁, h₁⟩ := hprop'
  exact topkis hfun (fun x _ y _ => ⟨mem_univ _, mem_univ _⟩)
    ⟨p₀, mem_univ _, h₀⟩ ⟨p₁, mem_univ _, h₁⟩

/-- `φ ≤_P φ'` and `P ≤_P P'` imply the P-order for the penalized functions
`φ + ι_P ≤_P φ' + ι_{P'}` — how the paper folds the constraints into the
objective. -/
theorem pOrder_add_ind {φ φ' : (ι → ℝ) → ERealTop} {P P' : Set (ι → ℝ)}
    (hfun : POrder φ φ') (hset : POrderSet P P') :
    POrder (fun p => φ p + ind P p) (fun p => φ' p + ind P' p) := by
  intro p p'
  by_cases hp : p ∈ P
  · by_cases hp' : p' ∈ P'
    · obtain ⟨hmeet, hjoin⟩ := hset p hp p' hp'
      simpa [ind_of_mem hp, ind_of_mem hp', ind_of_mem hmeet, ind_of_mem hjoin]
        using hfun p p'
    · simp [ind_of_not_mem hp']
  · simp [ind_of_not_mem hp]

/-! ## Theorem 1: the dual of Topkis -/

/-- **Dual of Topkis (GHS Theorem 1).** If the penalized functions satisfy
`ψ + ι_Q ≤_Q ψ' + ι_{Q'}` and each objective is finite somewhere on its
feasible set, then `argmin_Q ψ ≤_Q argmin_{Q'} ψ'`. -/
theorem dual_topkis {ψ ψ' : (ι → ℝ) → ERealTop} {Q Q' : Set (ι → ℝ)}
    (h : QOrder (fun q => ψ q + ind Q q) (fun q => ψ' q + ind Q' q))
    (hprop : ∃ q ∈ Q, ψ q ≠ ⊤) (hprop' : ∃ q' ∈ Q', ψ' q' ≠ ⊤) :
    QOrderSet (argminOn ψ Q) (argminOn ψ' Q') := by
  rintro q ⟨hqQ, hqmin⟩ q' ⟨hq'Q', hq'min⟩ δ₁ hδ₁
  obtain ⟨q₀, hq₀, hfin₀⟩ := hprop
  obtain ⟨q₁, hq₁, hfin₁⟩ := hprop'
  have hψq : ψ q ≠ ⊤ := ne_top_of_le_ne_top hfin₀ (hqmin q₀ hq₀)
  have hψ'q' : ψ' q' ≠ ⊤ := ne_top_of_le_ne_top hfin₁ (hq'min q₁ hq₁)
  obtain ⟨δ₂, hδ₂, hkey⟩ := h q q' δ₁ hδ₁
  simp only [ind_of_mem hqQ, ind_of_mem hq'Q', add_zero] at hkey
  -- the finite right-hand side forces feasibility of both perturbed points
  have hne := ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hψq, hψ'q'⟩) hkey
  obtain ⟨hne1, hne2⟩ := WithTop.add_ne_top.mp hne
  have hmem1 : q - (δ₁ - δ₂) ∈ Q := by
    by_contra hmem
    rw [ind_of_not_mem hmem] at hne1
    simp at hne1
  have hmem2 : q' + (δ₁ - δ₂) ∈ Q' := by
    by_contra hmem
    rw [ind_of_not_mem hmem] at hne2
    simp at hne2
  simp only [ind_of_mem hmem1, ind_of_mem hmem2, add_zero] at hkey
  obtain ⟨e1, e2⟩ := eq_of_le_of_le_of_add_le_add hψq hψ'q'
    (hqmin _ hmem1) (hq'min _ hmem2) hkey
  refine ⟨δ₂, hδ₂, ⟨hmem1, fun z hz => ?_⟩, ⟨hmem2, fun z hz => ?_⟩⟩
  · rw [e1]; exact hqmin z hz
  · rw [e2]; exact hq'min z hz

/-- The paper's itemized hypothesis (for feasible `q, q'` and admissible `δ₁`
there is `δ₂` keeping both perturbed points feasible without increasing the
total cost) implies the Q-order of the penalized functions. -/
theorem qOrder_add_ind_of_exchange {ψ ψ' : (ι → ℝ) → ERealTop} {Q Q' : Set (ι → ℝ)}
    (h : ∀ q ∈ Q, ∀ q' ∈ Q', ∀ δ₁ ∈ Icc 0 ((q - q')⁺), ∃ δ₂ ∈ Icc 0 ((q - q')⁻),
      (q - (δ₁ - δ₂) ∈ Q ∧ q' + (δ₁ - δ₂) ∈ Q') ∧
        ψ (q - (δ₁ - δ₂)) + ψ' (q' + (δ₁ - δ₂)) ≤ ψ q + ψ' q') :
    QOrder (fun q => ψ q + ind Q q) (fun q => ψ' q + ind Q' q) := by
  intro q q' δ₁ hδ₁
  by_cases hq : q ∈ Q
  · by_cases hq' : q' ∈ Q'
    · obtain ⟨δ₂, hδ₂, ⟨hm1, hm2⟩, hle⟩ := h q hq q' hq' δ₁ hδ₁
      refine ⟨δ₂, hδ₂, ?_⟩
      simpa [ind_of_mem hq, ind_of_mem hq', ind_of_mem hm1, ind_of_mem hm2] using hle
    · exact ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, by simp [ind_of_not_mem hq']⟩
  · exact ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, by simp [ind_of_not_mem hq]⟩

/-- Unconstrained dual Topkis: `ψ ≤_Q ψ'` orders the global argmins in the
Q-order. -/
theorem dual_topkis_univ {ψ ψ' : (ι → ℝ) → ERealTop}
    (h : QOrder ψ ψ') (hprop : ∃ q, ψ q ≠ ⊤) (hprop' : ∃ q', ψ' q' ≠ ⊤) :
    QOrderSet (argminOn ψ univ) (argminOn ψ' univ) := by
  obtain ⟨q₀, h₀⟩ := hprop
  obtain ⟨q₁, h₁⟩ := hprop'
  refine dual_topkis ?_ ⟨q₀, mem_univ _, h₀⟩ ⟨q₁, mem_univ _, h₁⟩
  simpa using h

end GHS
