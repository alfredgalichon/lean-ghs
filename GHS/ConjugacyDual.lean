import GHS.Conjugacy
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Data.Fin.VecNotation

/-!
# GHS Phase 4 (item 11): the conjugacy theorem, P ⟹ Q direction (finite case)

The deep half of GHS Theorem 4 at `D = 𝒵`, no `ε`, for **finite-valued**
convex `f, g` on `ℝⁿ`:

* `qOrderE_coe_of_pOrder_fenchelConjugate` : if `g* ≤_P f*` then `f ≤_Q g`.

Proof (PQ-convexity lecture `app:duality` at `A = 0`, pair version, with the
min–max step replaced by conjugate duality): fix `q₁, q₂, δ₁` and minimize
`h(δ₂) = f(q₁-δ₁+δ₂) + g(q₂+δ₁-δ₂)` over the compact box `[0, (q₁-q₂)⁻]`.
A finite-dimensional perturbation argument proves the needed strong duality:
the box value function is finite, convex, and continuous, so a supporting
linear functional at zero produces the dual decomposition. The P-hypothesis
and the elementary estimate `dot_dual_bound` then give the exchange witness.

The extension to general closed proper convex `f, g` (via Pasch–Hausdorff
regularization) is the next step; see the roadmap.

This file depends only on Mathlib and the local `GHS.Rockafellar` layer.
-/

open Set

namespace GHS

variable {n : ℕ}

/-! ## EReal supremum helpers -/

theorem iSup_add_coe {α : Type*} [Nonempty α] (H : α → EReal) (k : ℝ) :
    (⨆ x, H x) + (k : EReal) = ⨆ x, (H x + (k : EReal)) := by
  calc (⨆ x, H x) + (k : EReal)
      = (⨆ _ : Unit, (k : EReal)) + (⨆ x, H x) := by rw [iSup_const, add_comm]
    _ = ⨆ p : Unit × α, ((k : EReal) + H p.2) :=
        section16_iSup_add_iSup_eq_iSup_prod _ H
    _ = ⨆ x, (H x + (k : EReal)) := by
        refine le_antisymm (iSup_le fun p => ?_) (iSup_le fun x => ?_)
        · rw [add_comm]
          exact le_iSup (fun x => H x + (k : EReal)) p.2
        · rw [add_comm]
          exact le_iSup (fun p : Unit × α => (k : EReal) + H p.2) ((), x)

theorem coe_sub_add_coe (A k : ℝ) (F : EReal) :
    (((A : ℝ) : EReal) - F) + ((k : ℝ) : EReal) = ((A + k : ℝ) : EReal) - F := by
  induction F using EReal.rec with
  | bot =>
    rw [EReal.sub_bot (EReal.coe_ne_bot A), EReal.sub_bot (EReal.coe_ne_bot (A + k)),
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot k)]
  | coe r =>
    norm_cast
    ring
  | top =>
    rw [EReal.sub_top, EReal.sub_top, EReal.bot_add]

/-! ## Conjugate formulas -/

/-- Conjugate of a translate: `(f(m + ·))* = f* - ⟨m, ·⟩`. -/
theorem fenchelConjugate_translate (f : (Fin n → ℝ) → EReal) (m v : Fin n → ℝ) :
    fenchelConjugate n (fun δ => f (m + δ)) v
      = fenchelConjugate n f v + ((-(m ⬝ᵥ v) : ℝ) : EReal) := by
  rw [fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup, iSup_add_coe]
  refine le_antisymm (iSup_le fun δ => ?_) (iSup_le fun x => ?_)
  · have h1 : ((δ ⬝ᵥ v : ℝ) : EReal) - f (m + δ)
        = ((((m + δ) ⬝ᵥ v : ℝ) : EReal) - f (m + δ)) + ((-(m ⬝ᵥ v) : ℝ) : EReal) := by
      rw [coe_sub_add_coe]
      congr 2
      rw [add_dotProduct]
      ring
    rw [h1]
    exact le_iSup
      (fun x => (((x ⬝ᵥ v : ℝ) : EReal) - f x) + ((-(m ⬝ᵥ v) : ℝ) : EReal)) (m + δ)
  · have hxm : m + (x - m) = x := by abel
    have h2 : (((x ⬝ᵥ v : ℝ) : EReal) - f x) + ((-(m ⬝ᵥ v) : ℝ) : EReal)
        = (((x - m) ⬝ᵥ v : ℝ) : EReal) - f x := by
      rw [coe_sub_add_coe]
      congr 2
      rw [sub_dotProduct]
      ring
    rw [h2]
    have h3 := le_iSup (fun δ => ((δ ⬝ᵥ v : ℝ) : EReal) - f (m + δ)) (x - m)
    rwa [hxm] at h3

/-- Conjugate of a reflected translate: `(g(b - ·))* = g*(-·) + ⟨b, ·⟩`. -/
theorem fenchelConjugate_reflectTranslate (g : (Fin n → ℝ) → EReal) (b v : Fin n → ℝ) :
    fenchelConjugate n (fun δ => g (b - δ)) v
      = fenchelConjugate n g (-v) + ((b ⬝ᵥ v : ℝ) : EReal) := by
  rw [fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup, iSup_add_coe]
  refine le_antisymm (iSup_le fun δ => ?_) (iSup_le fun x => ?_)
  · have h1 : ((δ ⬝ᵥ v : ℝ) : EReal) - g (b - δ)
        = ((((b - δ) ⬝ᵥ (-v) : ℝ) : EReal) - g (b - δ)) + ((b ⬝ᵥ v : ℝ) : EReal) := by
      rw [coe_sub_add_coe]
      congr 2
      rw [dotProduct_neg, sub_dotProduct]
      ring
    rw [h1]
    exact le_iSup
      (fun x => (((x ⬝ᵥ (-v) : ℝ) : EReal) - g x) + ((b ⬝ᵥ v : ℝ) : EReal)) (b - δ)
  · have hbx : b - (b - x) = x := by abel
    have h2 : (((x ⬝ᵥ (-v) : ℝ) : EReal) - g x) + ((b ⬝ᵥ v : ℝ) : EReal)
        = (((b - x) ⬝ᵥ v : ℝ) : EReal) - g x := by
      rw [coe_sub_add_coe]
      congr 2
      rw [dotProduct_neg, sub_dotProduct]
      ring
    rw [h2]
    have h3 := le_iSup (fun δ => ((δ ⬝ᵥ v : ℝ) : EReal) - g (b - δ)) (b - x)
    rwa [hbx] at h3

/-- Specialization of `fenchelConjugate_translate` to coerced real-valued
functions (stated so that `rw` matches syntactically). -/
theorem fenchelConjugate_translate_coe (f : (Fin n → ℝ) → ℝ) (m v : Fin n → ℝ) :
    fenchelConjugate n (fun δ => ((f (m + δ) : ℝ) : EReal)) v
      = fenchelConjugate n (fun x => ((f x : ℝ) : EReal)) v
        + ((-(m ⬝ᵥ v) : ℝ) : EReal) :=
  fenchelConjugate_translate (fun x => ((f x : ℝ) : EReal)) m v

/-- Specialization of `fenchelConjugate_reflectTranslate` to coerced
real-valued functions. -/
theorem fenchelConjugate_reflectTranslate_coe (g : (Fin n → ℝ) → ℝ) (b v : Fin n → ℝ) :
    fenchelConjugate n (fun δ => ((g (b - δ) : ℝ) : EReal)) v
      = fenchelConjugate n (fun x => ((g x : ℝ) : EReal)) (-v)
        + ((b ⬝ᵥ v : ℝ) : EReal) :=
  fenchelConjugate_reflectTranslate (fun x => ((g x : ℝ) : EReal)) b v

open Classical in
/-- The `EReal`-valued convex indicator. -/
noncomputable def indER (S : Set (Fin n → ℝ)) : (Fin n → ℝ) → EReal :=
  fun x => if x ∈ S then 0 else ⊤

/-- Conjugate of the box indicator: the support function `⟨c, v⁺⟩`. -/
theorem fenchelConjugate_indER_Icc (c v : Fin n → ℝ) (hc : 0 ≤ c) :
    fenchelConjugate n (indER (Icc 0 c)) v = ((∑ i, c i * (v i)⁺ : ℝ) : EReal) := by
  rw [fenchelConjugate_eq_iSup]
  obtain ⟨⟨s, hs, hval⟩, hub⟩ := isGreatest_boxDot_posPart v c hc
  refine le_antisymm (iSup_le fun δ => ?_) ?_
  · by_cases hδ : δ ∈ Icc (0 : Fin n → ℝ) c
    · rw [show indER (Icc 0 c) δ = 0 from if_pos hδ, sub_zero]
      exact EReal.coe_le_coe_iff.mpr (hub ⟨δ, hδ, rfl⟩)
    · rw [show indER (Icc 0 c) δ = ⊤ from if_neg hδ, EReal.sub_top]
      exact bot_le
  · have h1 := le_iSup (fun δ => ((δ ⬝ᵥ v : ℝ) : EReal) - indER (Icc 0 c) δ) s
    rw [show indER (Icc 0 c) s = 0 from if_pos hs, sub_zero] at h1
    have h2 : (s ⬝ᵥ v : ℝ) = ∑ i, c i * (v i)⁺ := hval
    rwa [h2] at h1

/-! ## Properness and effective domains -/

/-- A finite-valued convex function, coerced to `EReal`, is proper convex. -/
theorem properConvexOn_coe {f : (Fin n → ℝ) → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ProperConvexFunctionOn Set.univ (fun x => ((f x : ℝ) : EReal)) := by
  refine ⟨?_, ⟨(0, f 0), ⟨trivial, ?_⟩⟩, fun x _ => EReal.coe_ne_bot _⟩
  · show Convex ℝ (epigraph Set.univ fun x => ((f x : ℝ) : EReal))
    have hset : epigraph (Set.univ : Set (Fin n → ℝ)) (fun x => ((f x : ℝ) : EReal))
        = {p : (Fin n → ℝ) × ℝ | p.1 ∈ Set.univ ∧ f p.1 ≤ p.2} := by
      ext p
      constructor
      · rintro ⟨-, h⟩
        have h' : ((f p.1 : ℝ) : EReal) ≤ (p.2 : EReal) := h
        exact ⟨trivial, by exact_mod_cast h'⟩
      · rintro ⟨-, h⟩
        refine ⟨trivial, ?_⟩
        show ((f p.1 : ℝ) : EReal) ≤ (p.2 : EReal)
        exact_mod_cast h
    rw [hset]
    exact hf.convex_epigraph
  · show ((f 0 : ℝ) : EReal) ≤ ((f 0 : ℝ) : EReal)
    exact le_refl _

/-- The box indicator is proper convex. -/
theorem properConvexOn_indER_Icc (c : Fin n → ℝ) (hc : 0 ≤ c) :
    ProperConvexFunctionOn Set.univ (indER (Icc 0 c)) := by
  refine ⟨?_, ⟨(0, 0), ⟨trivial, ?_⟩⟩, fun x _ => ?_⟩
  · show Convex ℝ (epigraph Set.univ (indER (Icc 0 c)))
    have hset : epigraph (Set.univ : Set (Fin n → ℝ)) (indER (Icc 0 c))
        = (Icc (0 : Fin n → ℝ) c) ×ˢ (Ici (0 : ℝ)) := by
      ext p
      constructor
      · rintro ⟨-, h⟩
        by_cases hp : p.1 ∈ Icc (0 : Fin n → ℝ) c
        · rw [show indER (Icc 0 c) p.1 = 0 from if_pos hp] at h
          exact ⟨hp, by exact_mod_cast h⟩
        · rw [show indER (Icc 0 c) p.1 = ⊤ from if_neg hp] at h
          exact absurd (top_le_iff.mp h) (EReal.coe_ne_top p.2)
      · rintro ⟨hmem, h⟩
        refine ⟨trivial, ?_⟩
        rw [show indER (Icc 0 c) p.1 = 0 from if_pos hmem]
        exact_mod_cast h
    rw [hset]
    exact (convex_Icc _ _).prod (convex_Ici _)
  · show indER (Icc 0 c) 0 ≤ (((0 : ℝ)) : EReal)
    rw [show indER (Icc 0 c) 0 = 0 from if_pos ⟨le_refl _, hc⟩]
    exact_mod_cast le_refl (0 : ℝ)
  · show indER (Icc 0 c) x ≠ ⊥
    unfold indER
    split <;> simp

theorem effectiveDomain_coe (f : (Fin n → ℝ) → ℝ) :
    effectiveDomain Set.univ (fun x => ((f x : ℝ) : EReal)) = Set.univ := by
  rw [effectiveDomain_eq]
  ext x
  simp [EReal.coe_lt_top]

theorem effectiveDomain_indER (S : Set (Fin n → ℝ)) :
    effectiveDomain Set.univ (indER S) = S := by
  rw [effectiveDomain_eq]
  ext x
  by_cases hx : x ∈ S <;> simp [indER, hx]

/-! ## The elementary dual dot-product estimate -/

/-- Coordinatewise `δ₁ᵢ λᵢ ≤ (q₁-q₂)⁺ᵢ λᵢ⁺` summed, in the arrangement the
decomposition bound consumes. -/
theorem dot_dual_bound (q₁ q₂ δ₁ u₁ u₂ : Fin n → ℝ)
    (h0 : 0 ≤ δ₁) (h1 : δ₁ ≤ (q₁ - q₂)⁺) :
    (q₁ - δ₁) ⬝ᵥ u₁ + (q₂ + δ₁) ⬝ᵥ u₂
      ≤ q₁ ⬝ᵥ (u₁ ⊔ u₂) + q₂ ⬝ᵥ (u₁ ⊓ u₂)
        + ∑ i, (q₁ - q₂)⁻ i * ((u₂ - u₁) i)⁺ := by
  simp only [dotProduct, Pi.sub_apply, Pi.add_apply, Pi.inf_apply, Pi.sup_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [show (q₁ - q₂)⁻ i = (q₁ i - q₂ i)⁻ from rfl]
  have hd0 : (0:ℝ) ≤ δ₁ i := h0 i
  have hd1 : δ₁ i ≤ (q₁ i - q₂ i)⁺ := h1 i
  have hpm := posPart_sub_negPart (q₁ i - q₂ i)
  rcases le_total (u₁ i) (u₂ i) with hu | hu
  · rw [sup_eq_right.mpr hu, inf_eq_left.mpr hu,
      posPart_eq_self.mpr (by linarith : (0:ℝ) ≤ u₂ i - u₁ i)]
    nlinarith [mul_le_mul_of_nonneg_right hd1 (sub_nonneg.mpr hu), hpm,
      mul_nonneg (negPart_nonneg (q₁ i - q₂ i)) (sub_nonneg.mpr hu),
      mul_le_mul_of_nonneg_right hpm.le (sub_nonneg.mpr hu),
      mul_le_mul_of_nonneg_right hpm.ge (sub_nonneg.mpr hu)]
  · rw [sup_eq_left.mpr hu, inf_eq_right.mpr hu,
      posPart_eq_zero.mpr (by linarith : u₂ i - u₁ i ≤ 0), mul_zero, add_zero]
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hu)]

/-! ## The main theorem (finite case) -/

/-- **P ⟹ Q for finite-valued convex functions (GHS Theorem 4, deep
direction).** If `g* ≤_P f*` then `f ≤_Q g`. -/
theorem qOrderE_coe_of_pOrder_fenchelConjugate {f g : (Fin n → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g)
    (hP : POrderE (fenchelConjugate n (fun x => ((g x : ℝ) : EReal)))
      (fenchelConjugate n (fun x => ((f x : ℝ) : EReal)))) :
    QOrderE (fun x => ((f x : ℝ) : EReal)) (fun x => ((g x : ℝ) : EReal)) := by
  intro q₁ q₂ δ₁ hδ₁
  set c : Fin n → ℝ := (q₁ - q₂)⁻ with hc_def
  have hc : (0 : Fin n → ℝ) ≤ c := negPart_nonneg _
  set m : Fin n → ℝ := q₁ - δ₁ with hm_def
  set b : Fin n → ℝ := q₂ + δ₁ with hb_def
  have hcf : Continuous f := hf.locallyLipschitz.continuous
  have hcg : Continuous g := hg.locallyLipschitz.continuous
  let obj : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) → ℝ :=
    fun p δ => f (m + p.1 + δ) + g (b + p.2 - δ)
  have hex (p : (Fin n → ℝ) × (Fin n → ℝ)) :
      ∃ δ ∈ Icc (0 : Fin n → ℝ) c, ∀ z ∈ Icc (0 : Fin n → ℝ) c, obj p δ ≤ obj p z := by
    have hcont : Continuous (obj p) :=
      (hcf.comp ((continuous_const.add continuous_const).add continuous_id)).add
        (hcg.comp ((continuous_const.add continuous_const).sub continuous_id))
    exact (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := c)).exists_isMinOn
      ⟨0, le_rfl, hc⟩ hcont.continuousOn
  classical
  let d : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) := fun p => (hex p).choose
  have hdmem (p) : d p ∈ Icc (0 : Fin n → ℝ) c := (hex p).choose_spec.1
  have hdmin (p) {z} (hz : z ∈ Icc (0 : Fin n → ℝ) c) : obj p (d p) ≤ obj p z :=
    (hex p).choose_spec.2 z hz
  let V : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun p => obj p (d p)
  have hVmin (p) {z} (hz : z ∈ Icc (0 : Fin n → ℝ) c) : V p ≤ obj p z :=
    hdmin p hz
  have hVconv : ConvexOn ℝ Set.univ V := by
    refine ⟨convex_univ, fun p _ r _ s t hs ht hst => ?_⟩
    let z := s • d p + t • d r
    have hz : z ∈ Icc (0 : Fin n → ℝ) c := (convex_Icc 0 c) (hdmem p) (hdmem r) hs ht hst
    refine (hVmin (s • p + t • r) hz).trans ?_
    dsimp [V, obj, z]
    have hf' := hf.2 (Set.mem_univ (m + p.1 + d p))
      (Set.mem_univ (m + r.1 + d r)) hs ht hst
    have hg' := hg.2 (Set.mem_univ (b + p.2 - d p))
      (Set.mem_univ (b + r.2 - d r)) hs ht hst
    have hm : s • (m + p.1 + d p) + t • (m + r.1 + d r) =
        m + (s • p.1 + t • r.1) + (s • d p + t • d r) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hstm : (s + t) * m i = m i := by rw [hst, one_mul]
      linarith
    have hb : s • (b + p.2 - d p) + t • (b + r.2 - d r) =
        b + (s • p.2 + t • r.2) - (s • d p + t • d r) := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hstb : (s + t) * b i = b i := by rw [hst, one_mul]
      linarith
    rw [← hm, ← hb]
    calc
      f (s • (m + p.1 + d p) + t • (m + r.1 + d r)) +
          g (s • (b + p.2 - d p) + t • (b + r.2 - d r))
          ≤ (s * f (m + p.1 + d p) + t * f (m + r.1 + d r)) +
            (s * g (b + p.2 - d p) + t * g (b + r.2 - d r)) :=
            add_le_add hf' hg'
      _ = s * (f (m + p.1 + d p) + g (b + p.2 - d p)) +
            t * (f (m + r.1 + d r) + g (b + r.2 - d r)) := by ring
  have hVcont : Continuous V := hVconv.locallyLipschitz.continuous
  obtain ⟨L, hL⟩ := exists_linearSubgradient V hVconv hVcont (0, 0)
  let l₁ : (Fin n → ℝ) →ₗ[ℝ] ℝ := L.toLinearMap.comp (LinearMap.inl ℝ _ _)
  let l₂ : (Fin n → ℝ) →ₗ[ℝ] ℝ := L.toLinearMap.comp (LinearMap.inr ℝ _ _)
  let u₁ : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm l₁
  let u₂ : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm l₂
  have hLpair (y z : Fin n → ℝ) : L (y, z) = y ⬝ᵥ u₁ + z ⬝ᵥ u₂ := by
    have hsplit : (y, z) = (y, 0) + (0, z) := by ext <;> simp
    rw [hsplit, map_add]
    have h1 : l₁ y = u₁ ⬝ᵥ y := by
      change l₁ y = (dotProductEquiv ℝ (Fin n) u₁) y
      rw [show dotProductEquiv ℝ (Fin n) u₁ = l₁ from
        LinearEquiv.apply_symm_apply (dotProductEquiv ℝ (Fin n)) l₁]
    have h2 : l₂ z = u₂ ⬝ᵥ z := by
      change l₂ z = (dotProductEquiv ℝ (Fin n) u₂) z
      rw [show dotProductEquiv ℝ (Fin n) u₂ = l₂ from
        LinearEquiv.apply_symm_apply (dotProductEquiv ℝ (Fin n)) l₂]
    change l₁ y + l₂ z = _
    rw [h1, h2, dotProduct_comm, dotProduct_comm z]
  obtain ⟨s, hsbox, hsval⟩ := (isGreatest_boxDot_posPart (u₂ - u₁) c hc).1
  change s ⬝ᵥ (u₂ - u₁) = ∑ i, c i * ((u₂ - u₁) i)⁺ at hsval
  have hkey (x w : Fin n → ℝ) :
      V 0 + (x - m - s) ⬝ᵥ u₁ + (w - b + s) ⬝ᵥ u₂ ≤ f x + g w := by
    let p : (Fin n → ℝ) × (Fin n → ℝ) := (x - m - s, w - b + s)
    have hsub := hL p
    have hv := hVmin p hsbox
    have hsub' : V 0 + (x - m - s) ⬝ᵥ u₁ + (w - b + s) ⬝ᵥ u₂ ≤ V p := by
      simpa [p, hLpair, add_assoc] using hsub
    have hobj : obj p s = f x + g w := by dsimp [obj, p]; congr 2 <;> abel
    rw [hobj] at hv
    exact hsub'.trans hv
  set cf := fenchelConjugate n (fun x => ((f x : ℝ) : EReal))
  set cg := fenchelConjugate n (fun x => ((g x : ℝ) : EReal))
  have hupper : cf u₁ + cg u₂ ≤
      ((m ⬝ᵥ u₁ + b ⬝ᵥ u₂ - ∑ i, c i * ((u₂ - u₁) i)⁺ - V 0 : ℝ) : EReal) := by
    change fenchelConjugate n (fun x => ((f x : ℝ) : EReal)) u₁ +
      fenchelConjugate n (fun x => ((g x : ℝ) : EReal)) u₂ ≤ _
    rw [fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup,
      section16_iSup_add_iSup_eq_iSup_prod]
    refine iSup_le fun p => ?_
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    have hk := hkey p.1 p.2
    simp only [sub_dotProduct, add_dotProduct] at hk
    have hsval' : s ⬝ᵥ u₂ - s ⬝ᵥ u₁ = ∑ i, c i * ((u₂ - u₁) i)⁺ := by
      calc
        s ⬝ᵥ u₂ - s ⬝ᵥ u₁ = (u₂ - u₁) ⬝ᵥ s := by
          rw [sub_dotProduct, dotProduct_comm u₂, dotProduct_comm u₁]
        _ = s ⬝ᵥ (u₂ - u₁) := dotProduct_comm _ _
        _ = _ := hsval
    linarith [hsval']
  have hY1 : (((q₁ ⬝ᵥ (u₁ ⊔ u₂)) - f q₁ : ℝ) : EReal) ≤ cf (u₁ ⊔ u₂) := by
    change _ ≤ fenchelConjugate n (fun x => ((f x : ℝ) : EReal)) (u₁ ⊔ u₂)
    rw [fenchelConjugate_eq_iSup]
    simpa [← EReal.coe_sub] using le_iSup
      (fun x => ((x ⬝ᵥ (u₁ ⊔ u₂) : ℝ) : EReal) - ((f x : ℝ) : EReal)) q₁
  have hY2 : (((q₂ ⬝ᵥ (u₁ ⊓ u₂)) - g q₂ : ℝ) : EReal) ≤ cg (u₁ ⊓ u₂) := by
    change _ ≤ fenchelConjugate n (fun x => ((g x : ℝ) : EReal)) (u₁ ⊓ u₂)
    rw [fenchelConjugate_eq_iSup]
    simpa [← EReal.coe_sub] using le_iSup
      (fun x => ((x ⬝ᵥ (u₁ ⊓ u₂) : ℝ) : EReal) - ((g x : ℝ) : EReal)) q₂
  have hPu : cg (u₁ ⊓ u₂) + cf (u₁ ⊔ u₂) ≤ cg u₂ + cf u₁ := by
    simpa [inf_comm, sup_comm, cf, cg] using hP u₂ u₁
  have hlower :
      (((q₂ ⬝ᵥ (u₁ ⊓ u₂) - g q₂) + (q₁ ⬝ᵥ (u₁ ⊔ u₂) - f q₁) : ℝ) : EReal)
        ≤ cg u₂ + cf u₁ := by
    rw [EReal.coe_add]
    exact (add_le_add hY2 hY1).trans hPu
  have hdot := dot_dual_bound q₁ q₂ δ₁ u₁ u₂ hδ₁.1 hδ₁.2
  have hfinal : V 0 ≤ f q₁ + g q₂ := by
    have hu := hupper
    rw [add_comm] at hu
    have hboth := hlower.trans hu
    have hreal := EReal.coe_le_coe_iff.mp hboth
    rw [hc_def, hm_def, hb_def] at hreal
    change q₂ ⬝ᵥ (u₁ ⊓ u₂) - g q₂ + (q₁ ⬝ᵥ (u₁ ⊔ u₂) - f q₁) ≤
      (q₁ - δ₁) ⬝ᵥ u₁ + (q₂ + δ₁) ⬝ᵥ u₂ -
        ∑ i, (q₁ - q₂)⁻ i * ((u₂ - u₁) i)⁺ - V 0 at hreal
    linarith [hdot]
  let δ₂s := d (0, 0)
  have hδ₂mem : δ₂s ∈ Icc (0 : Fin n → ℝ) c := hdmem (0, 0)
  have hVzero : V 0 = f (q₁ - δ₁ + δ₂s) + g (q₂ + δ₁ - δ₂s) := by
    dsimp [V, obj, δ₂s]
    rw [hm_def, hb_def]
    congr 2 <;> abel
  rw [hVzero] at hfinal
  -- produce the exchange witness
  refine ⟨δ₂s, hδ₂mem, ?_⟩
  have harg1 : q₁ - (δ₁ - δ₂s) = q₁ - δ₁ + δ₂s := by abel
  have harg2 : q₂ + (δ₁ - δ₂s) = q₂ + δ₁ - δ₂s := by abel
  rw [harg1, harg2, ← EReal.coe_add, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr hfinal

end GHS
