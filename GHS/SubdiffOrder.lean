import GHS.PriceMCS
import GHS.SubdiffMCS
import GHS.Theorem4
import GHS.ConjugacyDual

/-!
# GHS Theorem 2, (4) implies (3): subdifferential order

This file closes the remaining arrow in the cycle `(1) ⇒ (4) ⇒ (3) ⇒ (2) ⇒ (1)`
for a finite-valued convex function `φ : ℝⁿ → ℝ`.

The proof has three layers:

* the G9 Fenchel--Young identity identifying subgradients with maximizers of
  `q ↦ p·q - c(q)`, where `c = φ*`, and its capacity/rejection form;
* the paper's construction `qb = q ⊔ q'`, which transports
  `qOrderSetD_capacity` from rejection sets to the subdifferentials;
* a direct maximal-transfer lemma for `QOrderSetD`, yielding the projected
  weak-set-order statement consumed by `submodular_of_subdiff_wso`.

No compactness of subdifferentials is required for the last layer: choosing the
entire positive discrepancy on the coordinates in `D` forces the transferred
point in the lower set to dominate the given point in the upper set on `D`.
-/

open Set

namespace GHS

variable {n : ℕ}

/-! ## G9: subgradients are the maximizers of the conjugate objective -/

/-- The cost whose conjugate is the finite convex function `φ`. -/
noncomputable def subdiffCost (φ : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → EReal :=
  fenchelConjugate n (fun p => ((φ p : ℝ) : EReal))

/-- A Fenchel conjugate of a finite convex function never takes `⊥`. -/
theorem subdiffCost_ne_bot {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (q : Fin n → ℝ) :
    subdiffCost φ q ≠ ⊥ :=
  fenchelConjugate_ne_bot_of_proper (properConvexOn_coe hφ) q

/-- The same conjugate, regarded as a `WithTop ℝ`-valued cost. -/
noncomputable def subdiffCostTop (φ : (Fin n → ℝ) → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) (q : Fin n → ℝ) : ERealTop :=
  (subdiffCost φ q).unbot (subdiffCost_ne_bot hφ q)

private theorem toE_eq_withBotCoe (a : ERealTop) :
    toE a = WithBot.some a := by
  induction a using WithTop.recTopCoe with
  | top => rfl
  | coe r => rfl

@[simp] theorem toE_subdiffCostTop {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (q : Fin n → ℝ) :
    toE (subdiffCostTop φ hφ q) = subdiffCost φ q := by
  rw [toE_eq_withBotCoe]
  exact WithBot.coe_unbot _ _

/-- Real submodularity of `φ` makes its conjugate cost exchangeable. -/
theorem exchangeable_subdiffCostTop {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ)
    (hsub : ∀ x y, φ (x ⊓ y) + φ (x ⊔ y) ≤ φ x + φ y) :
    Exchangeable (subdiffCostTop φ hφ) := by
  have hproper := properConvexOn_coe hφ
  have hlsc : LowerSemicontinuous (fun x => ((φ x : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hφ.locallyLipschitz.continuous).lowerSemicontinuous
  have hP : POrderE (fun x => ((φ x : ℝ) : EReal))
      (fun x => ((φ x : ℝ) : EReal)) := by
    intro x y
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact hsub x y
  have hcostLsc := (fenchelConjugate_closedConvex n
    (fun x => ((φ x : ℝ) : EReal))).1
  have hcostProper := fenchelConjugate_proper hlsc hproper
  have hbic := fenchelConjugate_biconjugate hlsc hproper
  have hP' : POrderE
      (fenchelConjugate n (subdiffCost φ))
      (fenchelConjugate n (subdiffCost φ)) := by
    simpa only [subdiffCost, hbic] using hP
  apply qOrderE_toE_iff.mp
  simpa only [toE_subdiffCostTop] using
    (qOrderE_iff_pOrderE_fenchelConjugate hcostLsc hcostProper
      hcostLsc hcostProper).mpr hP'

/-- Fenchel--Young equality in subgradient form. -/
theorem subgradient_iff_subdiffCost_eq {φ : (Fin n → ℝ) → ℝ}
    (_hφ : ConvexOn ℝ Set.univ φ) (p z : Fin n → ℝ) :
    Subgradient φ p z ↔ subdiffCost φ z = ((p ⬝ᵥ z - φ p : ℝ) : EReal) := by
  constructor
  · intro hz
    rw [subdiffCost, fenchelConjugate_eq_iSup]
    apply le_antisymm
    · refine iSup_le fun x => ?_
      have hreal : x ⬝ᵥ z - φ x ≤ p ⬝ᵥ z - φ p := by
        have h := hz x
        rw [dotProduct_sub] at h
        rw [dotProduct_comm z x, dotProduct_comm z p] at h
        linarith
      exact EReal.coe_le_coe_iff.mpr hreal
    · rw [EReal.coe_sub]
      exact le_iSup (fun x : Fin n → ℝ =>
        ((x ⬝ᵥ z : ℝ) : EReal) - ((φ x : ℝ) : EReal)) p
  · intro hz x
    have hterm : ((x ⬝ᵥ z : ℝ) : EReal) - ((φ x : ℝ) : EReal) ≤ subdiffCost φ z := by
      rw [subdiffCost, fenchelConjugate_eq_iSup]
      exact le_iSup (fun y : Fin n → ℝ =>
        ((y ⬝ᵥ z : ℝ) : EReal) - ((φ y : ℝ) : EReal)) x
    rw [hz] at hterm
    have hreal := EReal.coe_le_coe_iff.mp hterm
    rw [dotProduct_comm x z, dotProduct_comm p z] at hreal
    rw [dotProduct_sub]
    linarith

/-- **Erratum G9, unconstrained form.** A vector is a subgradient of `φ` at
`p` exactly when it maximizes `w ↦ p·w - φ*(w)` over the whole space. -/
theorem subgradient_iff_argmax {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p z : Fin n → ℝ) :
    Subgradient φ p z ↔
      ∀ w : Fin n → ℝ,
        ((w ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ w ≤
          ((z ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ z := by
  have hproper := properConvexOn_coe hφ
  have hlsc : LowerSemicontinuous (fun x => ((φ x : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hφ.locallyLipschitz.continuous).lowerSemicontinuous
  have hbic := fenchelConjugate_biconjugate hlsc hproper
  have hupper (w : Fin n → ℝ) :
      ((w ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ w ≤ ((φ p : ℝ) : EReal) := by
    have hle := le_iSup (fun q : Fin n → ℝ =>
      ((q ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ q) w
    have hp := congrFun hbic p
    simpa [subdiffCost, dotProduct_comm] using hle.trans_eq hp
  constructor
  · intro hz w
    have hcz := (subgradient_iff_subdiffCost_eq hφ p z).mp hz
    calc
      ((w ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ w ≤ ((φ p : ℝ) : EReal) := hupper w
      _ = ((z ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ z := by
        rw [hcz, dotProduct_comm z p, ← EReal.coe_sub]
        congr 1
        ring
  · intro hz
    obtain ⟨z₀, hz₀⟩ := exists_subgradient φ hφ p
    have hcz₀ := (subgradient_iff_subdiffCost_eq hφ p z₀).mp hz₀
    have hz₀val :
        ((z₀ ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ z₀ = ((φ p : ℝ) : EReal) := by
      rw [hcz₀, dotProduct_comm z₀ p, ← EReal.coe_sub]
      congr 1
      ring
    have hzval :
        ((z ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ z = ((φ p : ℝ) : EReal) :=
      le_antisymm (hupper z) (by rw [← hz₀val]; exact hz z₀)
    have hztop : subdiffCost φ z ≠ ⊤ := by
      intro htop
      rw [htop] at hzval
      simp at hzval
    have hzbot := subdiffCost_ne_bot hφ z
    lift subdiffCost φ z to ℝ using ⟨hztop, hzbot⟩ with r hr
    apply (subgradient_iff_subdiffCost_eq hφ p z).mpr
    rw [← hr]
    rw [← EReal.coe_sub] at hzval
    have hreal := EReal.coe_eq_coe_iff.mp hzval
    rw [dotProduct_comm z p] at hreal
    congr 1
    linarith

/-- The conjugate objective is bounded above by `φ p`. -/
theorem subdiffObjective_le {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p w : Fin n → ℝ) :
    ((w ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ w ≤ ((φ p : ℝ) : EReal) := by
  have hproper := properConvexOn_coe hφ
  have hlsc : LowerSemicontinuous (fun x => ((φ x : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hφ.locallyLipschitz.continuous).lowerSemicontinuous
  have hle := le_iSup (fun q : Fin n → ℝ =>
    ((q ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ q) w
  have hp := congrFun (fenchelConjugate_biconjugate hlsc hproper) p
  simpa [subdiffCost, dotProduct_comm] using hle.trans_eq hp

/-- At a subgradient the conjugate objective attains `φ p`. -/
theorem subdiffObjective_eq_of_subgradient {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {p z : Fin n → ℝ}
    (hz : Subgradient φ p z) :
    ((z ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ z = ((φ p : ℝ) : EReal) := by
  rw [(subgradient_iff_subdiffCost_eq hφ p z).mp hz, dotProduct_comm z p,
    ← EReal.coe_sub]
  congr 1
  ring

/-- Maximizers of the conjugate objective under the upper capacity `qb`. -/
def constrainedSubdiffArgmax (φ : (Fin n → ℝ) → ℝ)
    (p qb : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {z | z ≤ qb ∧ ∀ w, w ≤ qb →
    ((w ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ w ≤
      ((z ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ z}

/-- **Erratum G9, constrained form.** If one subgradient is feasible, the
capacity-constrained maximizers are exactly the feasible subgradients. -/
theorem constrainedSubdiffArgmax_eq {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {p qb z₀ : Fin n → ℝ}
    (hz₀ : Subgradient φ p z₀) (hz₀qb : z₀ ≤ qb) :
    constrainedSubdiffArgmax φ p qb =
      {z | Subgradient φ p z} ∩ {z | z ≤ qb} := by
  ext z
  constructor
  · rintro ⟨hzqb, hzmax⟩
    have hz₀val := subdiffObjective_eq_of_subgradient hφ hz₀
    have hzval :
        ((z ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ z = ((φ p : ℝ) : EReal) :=
      le_antisymm (subdiffObjective_le hφ p z) (by rw [← hz₀val]; exact hzmax z₀ hz₀qb)
    have hzglobal : ∀ w, ((w ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ w ≤
        ((z ⬝ᵥ p : ℝ) : EReal) - subdiffCost φ z := by
      intro w
      rw [hzval]
      exact subdiffObjective_le hφ p w
    exact ⟨(subgradient_iff_argmax hφ p z).mpr hzglobal, hzqb⟩
  · rintro ⟨hz, hzqb⟩
    exact ⟨hzqb, fun w _ => (subgradient_iff_argmax hφ p z).mp hz w⟩

/-- The transported cost is finite, with the Fenchel--Young value, at a subgradient. -/
theorem subdiffCostTop_eq_of_subgradient {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {p z : Fin n → ℝ}
    (hz : Subgradient φ p z) :
    subdiffCostTop φ hφ z = ((p ⬝ᵥ z - φ p : ℝ) : ERealTop) := by
  apply le_antisymm
  · rw [← toE_le_toE, toE_subdiffCostTop, toE_coe,
      (subgradient_iff_subdiffCost_eq hφ p z).mp hz]
  · rw [← toE_le_toE, toE_subdiffCostTop, toE_coe,
      (subgradient_iff_subdiffCost_eq hφ p z).mp hz]

/-- Every capacity objective is bounded below by the Fenchel--Young constant. -/
theorem capacityObjective_ge {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p qb u : Fin n → ℝ) :
    ((p ⬝ᵥ qb - φ p : ℝ) : ERealTop) ≤
      subdiffCostTop φ hφ (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) := by
  have hcost : ((p ⬝ᵥ (qb - u) - φ p : ℝ) : ERealTop) ≤
      subdiffCostTop φ hφ (qb - u) := by
    rw [← toE_le_toE, toE_coe, toE_subdiffCostTop,
      subdiffCost, fenchelConjugate_eq_iSup]
    rw [EReal.coe_sub]
    exact le_iSup (fun x : Fin n → ℝ =>
      ((x ⬝ᵥ (qb - u) : ℝ) : EReal) - ((φ x : ℝ) : EReal)) p
  calc
    ((p ⬝ᵥ qb - φ p : ℝ) : ERealTop) =
        ((p ⬝ᵥ (qb - u) - φ p : ℝ) : ERealTop) +
          ((p ⬝ᵥ u : ℝ) : ERealTop) := by
            rw [← WithTop.coe_add]
            congr 1
            rw [dotProduct_sub]
            ring
    _ ≤ subdiffCostTop φ hφ (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) :=
      add_le_add hcost le_rfl

theorem capacityObjective_eq_of_subgradient {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {p qb z : Fin n → ℝ}
    (hz : Subgradient φ p z) :
    subdiffCostTop φ hφ (qb - (qb - z)) +
        ((p ⬝ᵥ (qb - z) : ℝ) : ERealTop) =
      ((p ⬝ᵥ qb - φ p : ℝ) : ERealTop) := by
  rw [show qb - (qb - z) = z by abel, subdiffCostTop_eq_of_subgradient hφ hz,
    ← WithTop.coe_add]
  congr 1
  rw [dotProduct_sub]
  ring

/-- Rejected bundles for the conjugate cost. -/
def subdiffRejections (φ : (Fin n → ℝ) → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) (p qb : Fin n → ℝ) : Set (Fin n → ℝ) :=
  argminOn (fun u => subdiffCostTop φ hφ (qb - u) +
    ((p ⬝ᵥ u : ℝ) : ERealTop)) {v | 0 ≤ v}

/-- **Erratum G9, rejection bridge.** Provided a feasible subgradient exists,
rejection minimizers are exactly complements of feasible subgradients. -/
theorem mem_subdiffRejections_iff {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {p qb z₀ u : Fin n → ℝ}
    (hz₀ : Subgradient φ p z₀) (hz₀qb : z₀ ≤ qb) :
    u ∈ subdiffRejections φ hφ p qb ↔
      0 ≤ u ∧ Subgradient φ p (qb - u) := by
  let obj : (Fin n → ℝ) → ERealTop := fun v =>
    subdiffCostTop φ hφ (qb - v) + ((p ⬝ᵥ v : ℝ) : ERealTop)
  let K : ERealTop := ((p ⬝ᵥ qb - φ p : ℝ) : ERealTop)
  have hlower (v : Fin n → ℝ) : K ≤ obj v := capacityObjective_ge hφ p qb v
  have hvalue {z : Fin n → ℝ} (hz : Subgradient φ p z) : obj (qb - z) = K := by
    dsimp [obj, K]
    rw [show qb - (qb - z) = z by abel, subdiffCostTop_eq_of_subgradient hφ hz,
      ← WithTop.coe_add]
    congr 1
    rw [dotProduct_sub]
    ring
  constructor
  · rintro ⟨hu, hmin⟩
    have hv₀ : 0 ≤ qb - z₀ := by intro i; dsimp; linarith [hz₀qb i]
    have hobj : obj u = K :=
      le_antisymm (by rw [← hvalue hz₀]; exact hmin (qb - z₀) hv₀) (hlower u)
    have hcostEq : subdiffCostTop φ hφ (qb - u) =
        ((p ⬝ᵥ (qb - u) - φ p : ℝ) : ERealTop) := by
      apply le_antisymm
      · have hadd :
            subdiffCostTop φ hφ (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≤
              ((p ⬝ᵥ (qb - u) - φ p : ℝ) : ERealTop) +
                ((p ⬝ᵥ u : ℝ) : ERealTop) := by
          change obj u ≤ _
          rw [hobj]
          change ((p ⬝ᵥ qb - φ p : ℝ) : ERealTop) ≤ _
          rw [← WithTop.coe_add]
          apply le_of_eq
          congr 1
          rw [dotProduct_sub]
          ring
        exact (WithTop.add_le_add_iff_right (WithTop.coe_ne_top)).mp hadd
      · rw [← toE_le_toE, toE_coe, toE_subdiffCostTop,
          subdiffCost, fenchelConjugate_eq_iSup, EReal.coe_sub]
        exact le_iSup (fun x : Fin n → ℝ =>
          ((x ⬝ᵥ (qb - u) : ℝ) : EReal) - ((φ x : ℝ) : EReal)) p
    have hcostE : subdiffCost φ (qb - u) =
        ((p ⬝ᵥ (qb - u) - φ p : ℝ) : EReal) := by
      rw [← toE_subdiffCostTop hφ (qb - u), hcostEq, toE_coe]
    exact ⟨hu, (subgradient_iff_subdiffCost_eq hφ p (qb - u)).mpr hcostE⟩
  · rintro ⟨hu, hz⟩
    refine ⟨hu, fun v _ => ?_⟩
    change obj u ≤ obj v
    rw [show obj u = K by
      have he := hvalue hz
      rw [show qb - (qb - u) = u by abel] at he
      exact he]
    exact hlower v

/-- The literal bridge requested in G9: complementing by `qb` identifies
rejection minimizers with the capacity-constrained conjugate argmax. -/
theorem mem_subdiffRejections_iff_constrainedArgmax
    {φ : (Fin n → ℝ) → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    {p qb z₀ u : Fin n → ℝ} (hz₀ : Subgradient φ p z₀) (hz₀qb : z₀ ≤ qb) :
    u ∈ subdiffRejections φ hφ p qb ↔
      qb - u ∈ constrainedSubdiffArgmax φ p qb := by
  rw [mem_subdiffRejections_iff hφ hz₀ hz₀qb,
    constrainedSubdiffArgmax_eq hφ hz₀ hz₀qb]
  constructor
  · rintro ⟨hu, hsub⟩
    refine ⟨hsub, ?_⟩
    intro i
    have hui : (0 : ℝ) ≤ u i := hu i
    dsimp
    linarith
  · rintro ⟨hsub, hcap⟩
    refine ⟨?_, hsub⟩
    intro i
    have hcapi := hcap i
    dsimp at hcapi ⊢
    linarith

/-! ## The paper's `qb = q ⊔ q'` construction -/

/-- Submodularity orders the two subdifferentials in the paper's projected
`D`-restricted Q-order.  This is Theorem 2's missing `(4) ⇒ (3)` construction,
after item (4) is supplied by `qOrderSetD_capacity`. -/
theorem qOrderSetD_subgradient {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ)
    (hsub : ∀ a b, φ (a ⊓ b) + φ (a ⊔ b) ≤ φ a + φ b)
    {p p' : Fin n → ℝ} (hpp' : p ≤ p') :
    QOrderSetD {i | p i = p' i}
      {z | Subgradient φ p' z} {z | Subgradient φ p z} := by
  intro x hx y hy δ₁ hδ₁ hδ₁D
  let qb : Fin n → ℝ := y ⊔ x
  have hyqb : y ≤ qb := le_sup_left
  have hxqb : x ≤ qb := le_sup_right
  have hnonnegY : 0 ≤ qb - y := by intro i; dsimp; linarith [hyqb i]
  have hnonnegX : 0 ≤ qb - x := by intro i; dsimp; linarith [hxqb i]
  have hprop : ∃ u ∈ {v : Fin n → ℝ | 0 ≤ v},
      subdiffCostTop φ hφ (qb - u) + ((p ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤ := by
    refine ⟨qb - y, hnonnegY, ?_⟩
    rw [capacityObjective_eq_of_subgradient hφ hy]
    exact WithTop.coe_ne_top
  have hprop' : ∃ u ∈ {v : Fin n → ℝ | 0 ≤ v},
      subdiffCostTop φ hφ (qb - u) + ((p' ⬝ᵥ u : ℝ) : ERealTop) ≠ ⊤ := by
    refine ⟨qb - x, hnonnegX, ?_⟩
    rw [capacityObjective_eq_of_subgradient hφ hx]
    exact WithTop.coe_ne_top
  have hR := qOrderSetD_capacity (exchangeable_subdiffCostTop hφ hsub)
    hpp' (le_refl qb) hprop hprop'
  have hry : qb - y ∈ subdiffRejections φ hφ p qb :=
    (mem_subdiffRejections_iff hφ hy hyqb).2
      ⟨hnonnegY, by simpa only [sub_sub_cancel] using hy⟩
  have hrx : qb - x ∈ subdiffRejections φ hφ p' qb :=
    (mem_subdiffRejections_iff hφ hx hxqb).2
      ⟨hnonnegX, by simpa only [sub_sub_cancel] using hx⟩
  have hdiff : (qb - y) - (qb - x) = x - y := by abel
  have hδ₁R : δ₁ ∈ Icc 0 (((qb - y) - (qb - x))⁺) := by
    rw [hdiff]
    exact hδ₁
  obtain ⟨δ₂, hδ₂R, hry', hrx'⟩ := hR (qb - y) hry (qb - x) hrx δ₁ hδ₁R hδ₁D
  have hδ₂ : ∀ i ∈ {i | p i = p' i}, δ₂ i ∈ Icc 0 ((x - y)⁻ i) := by
    intro i hi
    rw [← hdiff]
    exact hδ₂R i hi
  have hy' : Subgradient φ p (y + δ₁ - δ₂) := by
    have h := (mem_subdiffRejections_iff hφ hy hyqb).1 hry'
    convert h.2 using 1
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hx' : Subgradient φ p' (x - δ₁ + δ₂) := by
    have h := (mem_subdiffRejections_iff hφ hx hxqb).1 hrx'
    convert h.2 using 1
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  exact ⟨δ₂, hδ₂, hx', hy'⟩

/-! ## A direct D-restricted weak-set-order consequence -/

/-- The one-sided weak-set-order consequence needed for subdifferentials.
For a `D`-restricted Q-order, every point of the first set is dominated on `D`
by some point of the second set, provided the second set is nonempty. -/
theorem qOrderSetD_exists_ge_on {D : Set (Fin n)} {X Y : Set (Fin n → ℝ)}
    (hQ : QOrderSetD D X Y) (hY : Y.Nonempty) :
    ∀ x ∈ X, ∃ y ∈ Y, ∀ i ∈ D, x i ≤ y i := by
  intro x hx
  obtain ⟨y, hy⟩ := hY
  classical
  let δ₁ : Fin n → ℝ := fun i => if i ∈ D then (x - y)⁺ i else 0
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

/-- The `D`-restricted subdifferential order implies the projected weak-set-order
statement used by `submodular_of_subdiff_wso`. -/
theorem subdiff_wso_of_submodular {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ)
    (hsub : ∀ x y, φ (x ⊓ y) + φ (x ⊔ y) ≤ φ x + φ y) :
    ∀ p p' : Fin n → ℝ, p ≤ p' → ∀ q', Subgradient φ p' q' →
      ∃ q, Subgradient φ p q ∧ ∀ i, p i = p' i → q' i ≤ q i := by
  intro p p' hpp' q' hq'
  obtain ⟨q₀, hq₀⟩ := exists_subgradient φ hφ p
  have hY : ({q | Subgradient φ p q} : Set (Fin n → ℝ)).Nonempty := ⟨q₀, hq₀⟩
  obtain ⟨q, hq, hdom⟩ := qOrderSetD_exists_ge_on
    (qOrderSetD_subgradient hφ hsub hpp') hY q' hq'
  exact ⟨q, hq, fun i hi => hdom i hi⟩

/-- **GHS Theorem 2, finite-valued convex case.** Real submodularity is
equivalent to the projected weak-set-order property of the subdifferential.
Together with `qOrderSetD_subgradient`, this closes
`(1) ⇒ (4) ⇒ (3) ⇒ (2) ⇒ (1)`. -/
theorem submodular_iff_subdiff_wso {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) :
    (∀ x y, φ (x ⊓ y) + φ (x ⊔ y) ≤ φ x + φ y) ↔
      ∀ p p' : Fin n → ℝ, p ≤ p' → ∀ q', Subgradient φ p' q' →
        ∃ q, Subgradient φ p q ∧ ∀ i, p i = p' i → q' i ≤ q i := by
  constructor
  · exact subdiff_wso_of_submodular hφ
  · intro h3 x y
    exact submodular_of_subdiff_wso hφ h3 x y

end GHS
