import GHS.Orders
import GHS.Rockafellar
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

/-!
# GHS Theorem 2, (3) ⟹ (2): subdifferential monotonicity implies submodularity

The last hard implication of GHS Theorem 2 (thm:FullMCS), for **finite-valued**
conjugates `φ = c*`.  The paper's hypothesis (3) — the projected
subdifferentials `Π_{p=p'} ∂c*(p)` Q-ordered along `p ≤ p'` — is taken here in
its **projected weak-set-order form** `(3')`:

> for `p ≤ p'`, every `q' ∈ ∂φ(p')` is dominated on the coincidence set
> `{i : p i = p' i}` by some `q ∈ ∂φ(p)`,

which the paper's (3) implies (Q-order ⟹ weak set order, Proposition 2 —
subdifferentials of a finite convex function are nonempty compact convex), so
proving `(3') ⟹ (2)` is stronger than the paper's step.  The paper's own
write-up of this step is garbled (erratum G2); the argument here repairs it:

* `dirDeriv` — the one-sided directional derivative
  `φ'(p; d) = inf_{t>0} (φ(p + t d) - φ(p))/t` of a finite convex `φ`, with
  the slope monotonicity calculus;
* `exists_subgradient_dirDeriv` — the **max formula**: `φ'(p; d)` is attained
  as `q ⬝ᵥ d` for some `q ∈ ∂φ(p)`.  Instead of topology, this applies the
  Rockafellar-layer `exists_subgradient` to the finite sublinear function
  `z ↦ φ'(p; z)` itself — the linear functional it produces at `d` is exact
  at `d` and globally below `φ'(p; ·)`, hence a subgradient of `φ` at `p`;
* `submodular_of_subdiff_wso` — **(3') ⟹ (2)**: submodularity via a
  telescoping comparison of the two parallel segments `x → x ⊔ y` and
  `x ⊓ y → y` (both with direction `d = y - x ⊓ y ≥ 0`, supported where
  `x ⊓ y` and `x` agree): each chord of the upper segment is below the
  matching (shifted) chord of the lower one, and the shift vanishes in the
  limit by continuity — no integration of derivatives is needed.

The finiteness of `c*` is a real hypothesis discovered by the formalization:
for `+∞`-valued conjugates the segment argument needs `dom c*` conditions
(the sublattice issue flagged in erratum G2).

Mathlib-only (part of the standalone `GHS` target).
-/

open Set Filter Topology

namespace GHS

variable {n : ℕ}

/-! ## Slopes and the directional derivative -/

/-- The slope of `φ` from `p` in direction `d` at step `t`. -/
noncomputable def dslope (φ : (Fin n → ℝ) → ℝ) (p d : Fin n → ℝ) (t : ℝ) :
    ℝ :=
  (φ (p + t • d) - φ p) / t

/-- The one-sided directional derivative of a finite convex function. -/
noncomputable def dirDeriv (φ : (Fin n → ℝ) → ℝ) (p d : Fin n → ℝ) : ℝ :=
  sInf (dslope φ p d '' Set.Ioi 0)

theorem dslope_mono {φ : (Fin n → ℝ) → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (p d : Fin n → ℝ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    dslope φ p d s ≤ dslope φ p d t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  set a : ℝ := s / t with ha_def
  have ha0 : 0 ≤ a := le_of_lt (div_pos hs ht)
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one ht]
    exact hst
  have hat : a * t = s := div_mul_cancel₀ s ht.ne'
  have hcomb : (1 - a) • p + a • (p + t • d) = p + s • d := by
    funext i
    show (1 - a) * p i + a * (p i + t * d i) = p i + s * d i
    linear_combination (d i) * hat
  have hconv := hφ.2 (Set.mem_univ p) (Set.mem_univ (p + t • d))
    (by linarith : (0:ℝ) ≤ 1 - a) ha0 (by ring)
  rw [hcomb] at hconv
  simp only [smul_eq_mul] at hconv
  rw [dslope, dslope, div_le_div_iff₀ hs ht]
  have h1 : φ (p + s • d) - φ p ≤ a * (φ (p + t • d) - φ p) := by linarith
  calc (φ (p + s • d) - φ p) * t
      ≤ (a * (φ (p + t • d) - φ p)) * t :=
        mul_le_mul_of_nonneg_right h1 ht.le
    _ = (φ (p + t • d) - φ p) * s := by
        rw [show (a * (φ (p + t • d) - φ p)) * t
          = (φ (p + t • d) - φ p) * (a * t) from by ring, hat]

theorem dotProduct_le_dslope {φ : (Fin n → ℝ) → ℝ} {p q : Fin n → ℝ}
    (hq : Subgradient φ p q) (d : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    q ⬝ᵥ d ≤ dslope φ p d t := by
  have h := hq (p + t • d)
  have h2 : p + t • d - p = t • d := by abel
  rw [h2] at h
  have h3 : q ⬝ᵥ (t • d) = t * (q ⬝ᵥ d) := by
    rw [dotProduct_smul, smul_eq_mul]
  rw [h3] at h
  rw [dslope, le_div_iff₀ ht]
  linarith

theorem nonempty_dslope_image (φ : (Fin n → ℝ) → ℝ) (p d : Fin n → ℝ) :
    (dslope φ p d '' Set.Ioi 0).Nonempty :=
  ⟨_, 1, Set.mem_Ioi.mpr one_pos, rfl⟩

theorem bddBelow_dslope_image {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p d : Fin n → ℝ) :
    BddBelow (dslope φ p d '' Set.Ioi 0) := by
  obtain ⟨q, hq⟩ := exists_subgradient φ hφ p
  refine ⟨q ⬝ᵥ d, ?_⟩
  rintro r ⟨t, ht, rfl⟩
  exact dotProduct_le_dslope hq d ht

theorem dirDeriv_le_dslope {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p d : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    dirDeriv φ p d ≤ dslope φ p d t :=
  csInf_le (bddBelow_dslope_image hφ p d) ⟨t, ht, rfl⟩

theorem dotProduct_le_dirDeriv {φ : (Fin n → ℝ) → ℝ} {p q : Fin n → ℝ}
    (hq : Subgradient φ p q) (d : Fin n → ℝ) :
    q ⬝ᵥ d ≤ dirDeriv φ p d := by
  refine le_csInf (nonempty_dslope_image φ p d) ?_
  rintro r ⟨t, ht, rfl⟩
  exact dotProduct_le_dslope hq d ht

theorem dirDeriv_zero (φ : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) :
    dirDeriv φ p 0 = 0 := by
  have h : dslope φ p 0 '' Set.Ioi 0 = {0} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact ⟨1, Set.mem_Ioi.mpr one_pos, by simp [dslope]⟩
    · rintro r ⟨t, ht, rfl⟩
      simp [dslope]
  rw [dirDeriv, h, csInf_singleton]

theorem dirDeriv_smul {φ : (Fin n → ℝ) → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (p d : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    dirDeriv φ p (c • d) = c * dirDeriv φ p d := by
  have key : ∀ t : ℝ, 0 < t →
      dslope φ p (c • d) t = c * dslope φ p d (t * c) := by
    intro t ht
    rw [dslope, dslope, smul_smul]
    field_simp
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hεc : 0 < ε / c := div_pos hε hc
    obtain ⟨r, ⟨s, hs, rfl⟩, hr⟩ :=
      exists_lt_of_csInf_lt (nonempty_dslope_image φ p d)
        (show dirDeriv φ p d < dirDeriv φ p d + ε / c by linarith)
    have h1 : dirDeriv φ p (c • d) ≤ dslope φ p (c • d) (s / c) :=
      dirDeriv_le_dslope hφ p _ (div_pos hs hc)
    rw [key _ (div_pos hs hc), div_mul_cancel₀ s hc.ne'] at h1
    have h2 : c * dslope φ p d s ≤ c * (dirDeriv φ p d + ε / c) :=
      mul_le_mul_of_nonneg_left hr.le hc.le
    have h3 : c * (dirDeriv φ p d + ε / c) = c * dirDeriv φ p d + ε := by
      field_simp
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨r, ⟨s, hs, rfl⟩, hr⟩ :=
      exists_lt_of_csInf_lt (nonempty_dslope_image φ p (c • d))
        (show dirDeriv φ p (c • d) < dirDeriv φ p (c • d) + ε by linarith)
    have h1 : dirDeriv φ p d ≤ dslope φ p d (s * c) :=
      dirDeriv_le_dslope hφ p _ (mul_pos hs hc)
    rw [key s hs] at hr
    have h2 : c * dslope φ p d (s * c) < dirDeriv φ p (c • d) + ε := hr
    have h3 : c * dirDeriv φ p d ≤ c * dslope φ p d (s * c) :=
      mul_le_mul_of_nonneg_left h1 hc.le
    linarith

theorem dirDeriv_convex_comb {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p d₁ d₂ : Fin n → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    dirDeriv φ p (a • d₁ + b • d₂)
      ≤ a * dirDeriv φ p d₁ + b * dirDeriv φ p d₂ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨r₁, ⟨t₁, ht₁, rfl⟩, hr₁⟩ :=
    exists_lt_of_csInf_lt (nonempty_dslope_image φ p d₁)
      (show dirDeriv φ p d₁ < dirDeriv φ p d₁ + ε by linarith)
  obtain ⟨r₂, ⟨t₂, ht₂, rfl⟩, hr₂⟩ :=
    exists_lt_of_csInf_lt (nonempty_dslope_image φ p d₂)
      (show dirDeriv φ p d₂ < dirDeriv φ p d₂ + ε by linarith)
  have ht : 0 < min t₁ t₂ := lt_min ht₁ ht₂
  have hq1 : dslope φ p d₁ (min t₁ t₂) ≤ dslope φ p d₁ t₁ :=
    dslope_mono hφ p d₁ ht (min_le_left _ _)
  have hq2 : dslope φ p d₂ (min t₁ t₂) ≤ dslope φ p d₂ t₂ :=
    dslope_mono hφ p d₂ ht (min_le_right _ _)
  have hcomb : dslope φ p (a • d₁ + b • d₂) (min t₁ t₂)
      ≤ a * dslope φ p d₁ (min t₁ t₂) + b * dslope φ p d₂ (min t₁ t₂) := by
    set t := min t₁ t₂
    have hpt : p + t • (a • d₁ + b • d₂)
        = a • (p + t • d₁) + b • (p + t • d₂) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(p i)) * hab
    have hconv := hφ.2 (Set.mem_univ (p + t • d₁))
      (Set.mem_univ (p + t • d₂)) ha hb hab
    simp only [smul_eq_mul] at hconv
    have habφ : a * φ p + b * φ p = φ p := by
      linear_combination (φ p) * hab
    have h : φ (p + t • (a • d₁ + b • d₂)) - φ p
        ≤ a * (φ (p + t • d₁) - φ p) + b * (φ (p + t • d₂) - φ p) := by
      rw [hpt]
      linarith
    rw [dslope, dslope, dslope]
    calc (φ (p + t • (a • d₁ + b • d₂)) - φ p) / t
        ≤ (a * (φ (p + t • d₁) - φ p) + b * (φ (p + t • d₂) - φ p)) / t := by
          gcongr
      _ = a * ((φ (p + t • d₁) - φ p) / t)
          + b * ((φ (p + t • d₂) - φ p) / t) := by ring
  have hstep := dirDeriv_le_dslope hφ p (a • d₁ + b • d₂) ht
  have h1 : a * dslope φ p d₁ (min t₁ t₂) ≤ a * dslope φ p d₁ t₁ :=
    mul_le_mul_of_nonneg_left hq1 ha
  have h2 : b * dslope φ p d₂ (min t₁ t₂) ≤ b * dslope φ p d₂ t₂ :=
    mul_le_mul_of_nonneg_left hq2 hb
  have h3 : a * dslope φ p d₁ t₁ ≤ a * (dirDeriv φ p d₁ + ε) :=
    mul_le_mul_of_nonneg_left hr₁.le ha
  have h4 : b * dslope φ p d₂ t₂ ≤ b * (dirDeriv φ p d₂ + ε) :=
    mul_le_mul_of_nonneg_left hr₂.le hb
  have h5 : a * (dirDeriv φ p d₁ + ε) + b * (dirDeriv φ p d₂ + ε)
      = a * dirDeriv φ p d₁ + b * dirDeriv φ p d₂ + ε := by
    linear_combination ε * hab
  linarith

theorem convexOn_dirDeriv {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (dirDeriv φ p) := by
  refine ⟨convex_univ, ?_⟩
  intro d₁ _ d₂ _ a b ha hb hab
  simpa [smul_eq_mul] using dirDeriv_convex_comb hφ p d₁ d₂ ha hb hab

/-! ## The max formula -/

/-- **The max formula**: the directional derivative of a finite convex
function is attained by a subgradient, `φ'(p; d) = q ⬝ᵥ d` with
`q ∈ ∂φ(p)`.  Proof: apply `exists_subgradient` to the finite sublinear
function `z ↦ φ'(p; z)` at `d`. -/
theorem exists_subgradient_dirDeriv {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p d : Fin n → ℝ) :
    ∃ q, Subgradient φ p q ∧ q ⬝ᵥ d = dirDeriv φ p d := by
  obtain ⟨q, hq⟩ := exists_subgradient (dirDeriv φ p) (convexOn_dirDeriv hφ p) d
  have hqd_ge : dirDeriv φ p d ≤ q ⬝ᵥ d := by
    have h := hq 0
    rw [dirDeriv_zero] at h
    have h2 : q ⬝ᵥ (0 - d) = -(q ⬝ᵥ d) := by
      rw [zero_sub, dotProduct_neg]
    rw [h2] at h
    linarith
  have hsub : ∀ z, q ⬝ᵥ z ≤ dirDeriv φ p z := by
    intro z
    by_contra hcon
    push_neg at hcon
    have hc : 0 < q ⬝ᵥ z - dirDeriv φ p z := by linarith
    have hK : 0 ≤ q ⬝ᵥ d - dirDeriv φ p d := by linarith
    have hkey : ∀ t : ℝ, 0 < t →
        t * (q ⬝ᵥ z - dirDeriv φ p z) ≤ q ⬝ᵥ d - dirDeriv φ p d := by
      intro t ht
      have h := hq (t • z)
      rw [dirDeriv_smul hφ p z ht] at h
      have h2 : q ⬝ᵥ (t • z - d) = t * (q ⬝ᵥ z) - q ⬝ᵥ d := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [h2] at h
      nlinarith
    have h := hkey ((q ⬝ᵥ d - dirDeriv φ p d + 1)
      / (q ⬝ᵥ z - dirDeriv φ p z)) (by positivity)
    rw [div_mul_cancel₀ _ hc.ne'] at h
    linarith
  have hqsub : Subgradient φ p q := by
    intro w
    have h1 : q ⬝ᵥ (w - p) ≤ dirDeriv φ p (w - p) := hsub (w - p)
    have h2 : dirDeriv φ p (w - p) ≤ dslope φ p (w - p) 1 :=
      dirDeriv_le_dslope hφ p _ one_pos
    have h3 : dslope φ p (w - p) 1 = φ w - φ p := by
      rw [dslope, one_smul, div_one]
      have h : p + (w - p) = w := by abel
      rw [h]
    linarith
  exact ⟨q, hqsub, le_antisymm (hsub d) hqd_ge⟩

/-! ## Chord comparison along a segment -/

/-- Left-chord bound: a chord of the segment is below the (right)
directional derivative at its right endpoint. -/
theorem sub_le_dirDeriv {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (p d : Fin n → ℝ) {t₀ t₁ : ℝ}
    (h : t₀ < t₁) :
    φ (p + t₁ • d) - φ (p + t₀ • d)
      ≤ (t₁ - t₀) * dirDeriv φ (p + t₁ • d) d := by
  have hT : 0 < t₁ - t₀ := by linarith
  suffices h2 : (φ (p + t₁ • d) - φ (p + t₀ • d)) / (t₁ - t₀)
      ≤ dirDeriv φ (p + t₁ • d) d by
    rw [div_le_iff₀ hT] at h2
    linarith [h2]
  refine le_csInf (nonempty_dslope_image φ _ d) ?_
  rintro r ⟨s, hs, rfl⟩
  rw [Set.mem_Ioi] at hs
  have hTs : (0:ℝ) < t₁ - t₀ + s := by linarith
  set lam : ℝ := s / (t₁ - t₀ + s) with hlam_def
  have hlam0 : 0 ≤ lam := le_of_lt (div_pos hs hTs)
  have hlam1 : lam ≤ 1 := by
    rw [hlam_def, div_le_one hTs]
    linarith
  have hlamT : lam * (t₁ - t₀ + s) = s := div_mul_cancel₀ s hTs.ne'
  have hp2 : (p + t₁ • d) + s • d = p + (t₁ + s) • d := by
    rw [add_smul, ← add_assoc]
  have hcomb : lam • (p + t₀ • d) + (1 - lam) • (p + (t₁ + s) • d)
      = p + t₁ • d := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(d i)) * hlamT
  have hconv := hφ.2 (Set.mem_univ (p + t₀ • d))
    (Set.mem_univ (p + (t₁ + s) • d)) hlam0 (by linarith : (0:ℝ) ≤ 1 - lam)
    (by ring)
  rw [hcomb] at hconv
  simp only [smul_eq_mul] at hconv
  have hexp : (lam * φ (p + t₀ • d) + (1 - lam) * φ (p + (t₁ + s) • d))
      * (t₁ - t₀ + s)
      = (lam * (t₁ - t₀ + s)) * φ (p + t₀ • d)
        + ((1 - lam) * (t₁ - t₀ + s)) * φ (p + (t₁ + s) • d) := by ring
  have h1lam : (1 - lam) * (t₁ - t₀ + s) = t₁ - t₀ := by
    linear_combination (-1 : ℝ) * hlamT
  have hconv' : φ (p + t₁ • d) * (t₁ - t₀ + s)
      ≤ s * φ (p + t₀ • d) + (t₁ - t₀) * φ (p + (t₁ + s) • d) := by
    have h := mul_le_mul_of_nonneg_right hconv hTs.le
    rw [hexp, hlamT, h1lam] at h
    exact h
  rw [dslope, div_le_div_iff₀ hT hs, hp2]
  nlinarith [hconv']

/-! ## (3′) ⟹ (2): the main theorem -/

/-- **GHS Theorem 2, (3) ⟹ (2), finite-valued case.** If for all `p ≤ p'`
every subgradient of `φ` at `p'` is dominated on the coincidence set
`{i : p i = p' i}` by a subgradient at `p` — the projected weak-set-order
form of the paper's assertion (3), which (3) implies — then `φ` is
submodular. -/
theorem submodular_of_subdiff_wso {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ)
    (h3 : ∀ p p' : Fin n → ℝ, p ≤ p' → ∀ q', Subgradient φ p' q' →
      ∃ q, Subgradient φ p q ∧ ∀ i, p i = p' i → q' i ≤ q i)
    (x y : Fin n → ℝ) :
    φ (x ⊓ y) + φ (x ⊔ y) ≤ φ x + φ y := by
  set d : Fin n → ℝ := y - x ⊓ y with hd_def
  have hd0 : 0 ≤ d := by
    intro i
    have h : (x ⊓ y) i ≤ y i := inf_le_right (a := x) (b := y) i
    show (0:ℝ) ≤ y i - (x ⊓ y) i
    linarith
  have hxd : x + d = x ⊔ y := by
    funext i
    show x i + (y i - (x ⊓ y) i) = (x ⊔ y) i
    rw [Pi.inf_apply, Pi.sup_apply]
    rcases le_total (x i) (y i) with h | h
    · rw [inf_eq_left.mpr h, sup_eq_right.mpr h]
      ring
    · rw [inf_eq_right.mpr h, sup_eq_left.mpr h]
      ring
  have hinfd : x ⊓ y + d = y := by
    funext i
    show (x ⊓ y) i + (y i - (x ⊓ y) i) = y i
    ring
  -- the derivative comparison between the two parallel segments
  have hcomp : ∀ t : ℝ,
      dirDeriv φ (x + t • d) d ≤ dirDeriv φ (x ⊓ y + t • d) d := by
    intro t
    obtain ⟨q', hq', hq'd⟩ := exists_subgradient_dirDeriv hφ (x + t • d) d
    have hle : x ⊓ y + t • d ≤ x + t • d := by
      intro i
      have h : (x ⊓ y) i ≤ x i := inf_le_left (a := x) (b := y) i
      show (x ⊓ y) i + t * d i ≤ x i + t * d i
      linarith
    obtain ⟨q, hq, hdom⟩ := h3 _ _ hle q' hq'
    have hqq' : q' ⬝ᵥ d ≤ q ⬝ᵥ d := by
      simp only [dotProduct]
      refine Finset.sum_le_sum fun i _ => ?_
      have hdi : (0:ℝ) ≤ d i := hd0 i
      rcases eq_or_lt_of_le hdi with h0 | hpos
      · rw [← h0, mul_zero, mul_zero]
      · have hxiy : (x ⊓ y) i = x i := by
          rw [Pi.inf_apply]
          rcases le_total (x i) (y i) with h | h
          · exact inf_eq_left.mpr h
          · exfalso
            have hdi : d i = y i - (x ⊓ y) i := rfl
            rw [Pi.inf_apply, inf_eq_right.mpr h] at hdi
            rw [hdi] at hpos
            simp at hpos
        have hco : (x ⊓ y + t • d) i = (x + t • d) i := by
          show (x ⊓ y) i + t * d i = x i + t * d i
          rw [hxiy]
        have h := hdom i hco
        exact mul_le_mul_of_nonneg_right h hpos.le
    calc dirDeriv φ (x + t • d) d = q' ⬝ᵥ d := hq'd.symm
      _ ≤ q ⬝ᵥ d := hqq'
      _ ≤ dirDeriv φ (x ⊓ y + t • d) d := dotProduct_le_dirDeriv hq d
  -- the telescoping bound for each subdivision
  have hN : ∀ N : ℕ, 0 < N →
      φ (x ⊔ y) - φ x
        ≤ φ (x ⊓ y + (((N:ℝ) + 1) / (N:ℝ)) • d)
          - φ (x ⊓ y + (1 / (N:ℝ)) • d) := by
    intro N hNpos
    have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
    set G : ℕ → ℝ := fun k => φ (x + ((k:ℝ) / (N:ℝ)) • d) with hG_def
    set F : ℕ → ℝ := fun k => φ (x ⊓ y + ((k:ℝ) / (N:ℝ)) • d) with hF_def
    have hstep : ∀ k : ℕ, G (k + 1) - G k ≤ F (k + 2) - F (k + 1) := by
      intro k
      have ht01 : ((k:ℝ) / (N:ℝ)) < (((k:ℝ) + 1) / (N:ℝ)) := by
        rw [div_lt_div_iff₀ hNr hNr]
        nlinarith
      have hgap : (((k:ℝ) + 1) / (N:ℝ)) - ((k:ℝ) / (N:ℝ)) = 1 / (N:ℝ) := by
        rw [div_sub_div_same]
        norm_num
      have h1 : G (k + 1) - G k
          ≤ (1 / (N:ℝ)) * dirDeriv φ (x + (((k:ℝ) + 1) / (N:ℝ)) • d) d := by
        have h := sub_le_dirDeriv hφ x d ht01
        rw [hgap] at h
        simp only [hG_def]
        push_cast
        convert h using 3
      have h2 : (1 / (N:ℝ)) * dirDeriv φ (x + (((k:ℝ) + 1) / (N:ℝ)) • d) d
          ≤ (1 / (N:ℝ))
            * dirDeriv φ (x ⊓ y + (((k:ℝ) + 1) / (N:ℝ)) • d) d :=
        mul_le_mul_of_nonneg_left (hcomp _) (by positivity)
      have h3 : (1 / (N:ℝ))
            * dirDeriv φ (x ⊓ y + (((k:ℝ) + 1) / (N:ℝ)) • d) d
          ≤ F (k + 2) - F (k + 1) := by
        have hdd := dirDeriv_le_dslope hφ (x ⊓ y + (((k:ℝ) + 1) / (N:ℝ)) • d)
          d (t := 1 / (N:ℝ)) (by positivity)
        rw [dslope, le_div_iff₀ (by positivity : (0:ℝ) < 1 / (N:ℝ))] at hdd
        have hpt : x ⊓ y + (((k:ℝ) + 1) / (N:ℝ)) • d + (1 / (N:ℝ)) • d
            = x ⊓ y + (((k:ℝ) + 2) / (N:ℝ)) • d := by
          rw [add_assoc, ← add_smul]
          congr 2
          field_simp
          ring
        rw [hpt] at hdd
        simp only [hF_def]
        push_cast
        linarith [hdd]
      linarith
    have htelG : ∑ k ∈ Finset.range N, (G (k + 1) - G k) = G N - G 0 :=
      Finset.sum_range_sub G N
    have htelF : ∑ k ∈ Finset.range N, (F (k + 2) - F (k + 1))
        = F (N + 1) - F 1 := by
      have h := Finset.sum_range_sub (fun k => F (k + 1)) N
      simpa using h
    have hsum : G N - G 0 ≤ F (N + 1) - F 1 := by
      rw [← htelG, ← htelF]
      exact Finset.sum_le_sum fun k _ => hstep k
    have hGN : G N = φ (x ⊔ y) := by
      simp only [hG_def]
      rw [div_self hNr.ne', one_smul, hxd]
    have hG0 : G 0 = φ x := by
      simp only [hG_def]
      norm_num
    have hFN : F (N + 1) = φ (x ⊓ y + (((N:ℝ) + 1) / (N:ℝ)) • d) := by
      simp only [hF_def]
      push_cast
      ring_nf
    have hF1 : F 1 = φ (x ⊓ y + (1 / (N:ℝ)) • d) := by
      simp only [hF_def]
      norm_num
    rw [hGN, hG0, hFN, hF1] at hsum
    exact hsum
  -- pass to the limit
  have hcont : Continuous φ := hφ.locallyLipschitz.continuous
  have htend1 : Tendsto
      (fun m : ℕ => φ (x ⊓ y + ((((m:ℝ)+1) + 1) / ((m:ℝ)+1)) • d)) atTop
      (𝓝 (φ y)) := by
    have hθ : Tendsto (fun m : ℕ => (((m:ℝ)+1) + 1) / ((m:ℝ)+1)) atTop
        (𝓝 1) := by
      have h1 : ∀ m : ℕ, (((m:ℝ)+1) + 1) / ((m:ℝ)+1)
          = 1 + 1 / ((m:ℝ)+1) := by
        intro m
        have hm : ((m:ℝ)+1) ≠ 0 := by positivity
        field_simp
      have h2 : Tendsto (fun m : ℕ => 1 + 1 / ((m:ℝ)+1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h2
      exact h2.congr fun m => (h1 m).symm
    have hpath : Tendsto
        (fun m : ℕ => x ⊓ y + ((((m:ℝ)+1) + 1) / ((m:ℝ)+1)) • d) atTop
        (𝓝 (x ⊓ y + (1:ℝ) • d)) :=
      tendsto_const_nhds.add (hθ.smul_const d)
    rw [one_smul, hinfd] at hpath
    exact (hcont.tendsto y).comp hpath
  have htend2 : Tendsto
      (fun m : ℕ => φ (x ⊓ y + (1 / ((m:ℝ)+1)) • d)) atTop
      (𝓝 (φ (x ⊓ y))) := by
    have hθ : Tendsto (fun m : ℕ => 1 / ((m:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hpath : Tendsto (fun m : ℕ => x ⊓ y + (1 / ((m:ℝ)+1)) • d) atTop
        (𝓝 (x ⊓ y + (0:ℝ) • d)) :=
      tendsto_const_nhds.add (hθ.smul_const d)
    rw [zero_smul, add_zero] at hpath
    exact (hcont.tendsto _).comp hpath
  have hlim : Tendsto
      (fun m : ℕ => φ (x ⊓ y + ((((m:ℝ)+1) + 1) / ((m:ℝ)+1)) • d)
        - φ (x ⊓ y + (1 / ((m:ℝ)+1)) • d)) atTop
      (𝓝 (φ y - φ (x ⊓ y))) :=
    htend1.sub htend2
  have hbound : ∀ m : ℕ,
      φ (x ⊔ y) - φ x
        ≤ φ (x ⊓ y + ((((m:ℝ)+1) + 1) / ((m:ℝ)+1)) • d)
          - φ (x ⊓ y + (1 / ((m:ℝ)+1)) • d) := by
    intro m
    have h := hN (m + 1) (Nat.succ_pos m)
    push_cast at h
    exact h
  have hfin : φ (x ⊔ y) - φ x ≤ φ y - φ (x ⊓ y) :=
    ge_of_tendsto hlim (Eventually.of_forall hbound)
  linarith

/-- The conclusion in the GHS vocabulary: `(3') ⟹ φ` is `Submodular`
(values embedded in `ℝ ∪ {+∞}`). -/
theorem submodular_coe_of_subdiff_wso {φ : (Fin n → ℝ) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ)
    (h3 : ∀ p p' : Fin n → ℝ, p ≤ p' → ∀ q', Subgradient φ p' q' →
      ∃ q, Subgradient φ p q ∧ ∀ i, p i = p' i → q' i ≤ q i) :
    Submodular (fun p => ((φ p : ℝ) : ERealTop)) := by
  intro p p'
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  have h := submodular_of_subdiff_wso hφ h3 p p'
  linarith

end GHS
