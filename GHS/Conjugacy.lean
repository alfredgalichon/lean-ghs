import GHS.BoxCalculus
import ConvexAnalysis.FiniteDimensional

/-!
# GHS Phase 4 (item 11): the conjugacy theorem, Q ⟹ P direction

Theorem 4 of GHS (case `D = 𝒵`, no `ε`), pair version:
`f ≤_Q g ⟺ g* ≤_P f*` for closed proper convex `f, g` on `ℝⁿ`.

This file sets up the EReal-side vocabulary (`QOrderE`, `POrderE`), the bridge
from the `WithTop ℝ`-valued orders of `GHS/Orders.lean`
(`qOrder_iff_qOrderE_toE`, `pOrder_iff_pOrderE_toE`), and proves the
**elementary direction**:

* `pOrderE_fenchelConjugate_of_qOrderE` : `f ≤_Q g → g* ≤_P f*`,
  for any `f, g` that never take `⊥` — no convexity, closedness, or duality
  machinery needed.

The proof is a per-pair estimate discovered while porting the PQ-convexity
lecture's Appendix A (`app:duality`, `A = 0`) to the pair setting: for
`q₁ ∈ dom f`, `q₂ ∈ dom g` and `λ := p - p'`, apply the exchange property with
the *sign-selected* perturbation `δ₁ = 𝟙{λ > 0}·(q₁ - q₂)⁺` (`exDelta`); the
resulting transfer `d = δ₁ - δ₂` satisfies the coordinatewise inequality
`λ⁺ᵢ (q₁ - q₂)ᵢ ≤ λᵢ dᵢ` (`coord_exchange`), which makes the moved pair
`(q₁ - d, q₂ + d)` witness the P-inequality of the conjugates at `(p, p')`
(`dotProduct_exchange_bound` summed).

The converse (P ⟹ Q) is the deep direction; it uses finite-dimensional convex duality
and biconjugation, first for finite-valued `f, g`, then in general via
Pasch–Hausdorff regularization `f_L = f □ L‖·‖₁` (whose conjugate is
`f* + ι_{[-L,L]ⁿ}`, so the P-hypothesis is preserved — boxes are modular).

The convex-analysis vocabulary used here is provided by the Mathlib-only
`ConvexAnalysis.FiniteDimensional` layer.
-/

open Set

namespace GHS

variable {n : ℕ}

/-! ## EReal-side orders and the bridge from `WithTop ℝ` -/

/-- The Q-order for `EReal`-valued functions (cf. `GHS.QOrder`). -/
def QOrderE (f g : (Fin n → ℝ) → EReal) : Prop :=
  ∀ q q' : Fin n → ℝ, ∀ δ₁ ∈ Icc 0 ((q - q')⁺), ∃ δ₂ ∈ Icc 0 ((q - q')⁻),
    f (q - (δ₁ - δ₂)) + g (q' + (δ₁ - δ₂)) ≤ f q + g q'

/-- The P-order for `EReal`-valued functions (cf. `GHS.POrder`). -/
def POrderE (φ φ' : (Fin n → ℝ) → EReal) : Prop :=
  ∀ p p' : Fin n → ℝ, φ (p ⊓ p') + φ' (p ⊔ p') ≤ φ p + φ' p'

/-- The order- and addition-preserving embedding `WithTop ℝ ↪ EReal`. -/
noncomputable def toE : ERealTop → EReal :=
  WithTop.recTopCoe ⊤ (fun r => (r : EReal))

@[simp] theorem toE_top : toE (⊤ : ERealTop) = ⊤ := rfl

@[simp] theorem toE_coe (r : ℝ) : toE ((r : ℝ) : ERealTop) = (r : EReal) := rfl

theorem toE_ne_bot (a : ERealTop) : toE a ≠ ⊥ := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe r => simp

theorem toE_add (a b : ERealTop) : toE (a + b) = toE a + toE b := by
  induction a using WithTop.recTopCoe with
  | top =>
    rw [top_add, toE_top, EReal.top_add_of_ne_bot (toE_ne_bot b)]
  | coe r =>
    induction b using WithTop.recTopCoe with
    | top =>
      rw [add_top, toE_top, toE_coe, EReal.add_top_of_ne_bot (by simp)]
    | coe s =>
      rw [← WithTop.coe_add, toE_coe, toE_coe, toE_coe, EReal.coe_add]

theorem toE_le_toE {a b : ERealTop} : toE a ≤ toE b ↔ a ≤ b := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe s => simp
  | coe r =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe s => simp

/-- The `WithTop ℝ` Q-order coincides with the `EReal` Q-order through `toE`. -/
theorem qOrderE_toE_iff {f g : (Fin n → ℝ) → ERealTop} :
    QOrderE (fun q => toE (f q)) (fun q => toE (g q)) ↔ QOrder f g := by
  constructor
  · intro h q q' δ₁ hδ₁
    obtain ⟨δ₂, hδ₂, hkey⟩ := h q q' δ₁ hδ₁
    refine ⟨δ₂, hδ₂, ?_⟩
    rw [← toE_add, ← toE_add, toE_le_toE] at hkey
    exact hkey
  · intro h q q' δ₁ hδ₁
    obtain ⟨δ₂, hδ₂, hkey⟩ := h q q' δ₁ hδ₁
    refine ⟨δ₂, hδ₂, ?_⟩
    rw [← toE_add, ← toE_add, toE_le_toE]
    exact hkey

/-- The `WithTop ℝ` P-order coincides with the `EReal` P-order through `toE`. -/
theorem pOrderE_toE_iff {φ φ' : (Fin n → ℝ) → ERealTop} :
    POrderE (fun p => toE (φ p)) (fun p => toE (φ' p)) ↔ POrder φ φ' := by
  constructor
  · intro h p p'
    have := h p p'
    rw [← toE_add, ← toE_add, toE_le_toE] at this
    exact this
  · intro h p p'
    rw [← toE_add, ← toE_add, toE_le_toE]
    exact h p p'

/-! ## The sign-selected exchange perturbation -/

open Classical in
/-- The sign-selected perturbation `δ₁ = 𝟙{p - p' > 0} · (q₁ - q₂)⁺`. -/
noncomputable def exDelta (p p' q₁ q₂ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if 0 < p i - p' i then (q₁ - q₂)⁺ i else 0

theorem exDelta_mem (p p' q₁ q₂ : Fin n → ℝ) :
    exDelta p p' q₁ q₂ ∈ Icc 0 ((q₁ - q₂)⁺) := by
  constructor <;> intro i <;> unfold exDelta
  · show (0:ℝ) ≤ if 0 < p i - p' i then (q₁ - q₂)⁺ i else 0
    by_cases h : 0 < p i - p' i
    · rw [if_pos h]; exact posPart_nonneg ((q₁ - q₂) i)
    · rw [if_neg h]
  · show (if 0 < p i - p' i then (q₁ - q₂)⁺ i else 0) ≤ (q₁ - q₂)⁺ i
    by_cases h : 0 < p i - p' i
    · rw [if_pos h]
    · rw [if_neg h]; exact posPart_nonneg ((q₁ - q₂) i)

/-- Coordinatewise exchange inequality: with `l = pᵢ - p'ᵢ`, `a = (q₁ - q₂)ᵢ`
and `d = (𝟙{l>0}·a⁺) - d₂` for `0 ≤ d₂ ≤ a⁻`, one has
`q₂ᵢ·min(pᵢ,p'ᵢ) + q₁ᵢ·max(pᵢ,p'ᵢ) ≤ (q₂ᵢ + d)·pᵢ + (q₁ᵢ - d)·p'ᵢ`. -/
theorem coord_exchange (pi pi' q1 q2 d2 : ℝ) (hd0 : 0 ≤ d2)
    (hd : d2 ≤ (q1 - q2)⁻) :
    q2 * (pi ⊓ pi') + q1 * (pi ⊔ pi')
      ≤ (q2 + ((if 0 < pi - pi' then (q1 - q2)⁺ else 0) - d2)) * pi
        + (q1 - ((if 0 < pi - pi' then (q1 - q2)⁺ else 0) - d2)) * pi' := by
  have hpm := posPart_sub_negPart (q1 - q2)
  by_cases h : 0 < pi - pi'
  · rw [if_pos h]
    have hmin : pi ⊓ pi' = pi' := inf_eq_right.mpr (by linarith)
    have hmax : pi ⊔ pi' = pi := sup_eq_left.mpr (by linarith)
    rw [hmin, hmax]
    nlinarith [hd, hpm, h]
  · rw [if_neg h]
    push_neg at h
    have hmin : pi ⊓ pi' = pi := inf_eq_left.mpr (by linarith)
    have hmax : pi ⊔ pi' = pi' := sup_eq_right.mpr (by linarith)
    rw [hmin, hmax]
    nlinarith [hd0, h]

/-- Summed exchange inequality: the moved pair `(q₂ + d, q₁ - d)` with
`d = exDelta - δ₂` improves the lattice pairing. -/
theorem dotProduct_exchange_bound (p p' q₁ q₂ δ₂ : Fin n → ℝ)
    (hδ₂ : δ₂ ∈ Icc 0 ((q₁ - q₂)⁻)) :
    q₂ ⬝ᵥ (p ⊓ p') + q₁ ⬝ᵥ (p ⊔ p')
      ≤ (q₂ + (exDelta p p' q₁ q₂ - δ₂)) ⬝ᵥ p
        + (q₁ - (exDelta p p' q₁ q₂ - δ₂)) ⬝ᵥ p' := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := coord_exchange (p i) (p' i) (q₁ i) (q₂ i) (δ₂ i) (hδ₂.1 i) (hδ₂.2 i)
  simpa [exDelta, Pi.add_apply, Pi.sub_apply, Pi.inf_apply, Pi.sup_apply] using h

/-! ## Theorem 4, easy direction: `f ≤_Q g ⟹ g* ≤_P f*` -/

/-- **Q ⟹ P (GHS Theorem 4 / Claim 1, one direction).** If `f, g` never take
`⊥` and `f ≤_Q g`, then the Fenchel conjugates satisfy `g* ≤_P f*`.
Elementary: no convexity or duality needed. -/
theorem pOrderE_fenchelConjugate_of_qOrderE {f g : (Fin n → ℝ) → EReal}
    (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (hQ : QOrderE f g) :
    POrderE (fenchelConjugate n g) (fenchelConjugate n f) := by
  intro p p'
  rw [fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup,
    section16_iSup_add_iSup_eq_iSup_prod]
  refine iSup_le fun x => ?_
  obtain ⟨q₂, q₁⟩ := x
  show (((q₂ ⬝ᵥ (p ⊓ p') : ℝ) : EReal) - g q₂) + (((q₁ ⬝ᵥ (p ⊔ p') : ℝ) : EReal) - f q₁)
    ≤ fenchelConjugate n g p + fenchelConjugate n f p'
  by_cases hg2 : g q₂ = ⊤
  · rw [hg2, EReal.sub_top, EReal.bot_add]
    exact bot_le
  by_cases hf1 : f q₁ = ⊤
  · rw [hf1, EReal.sub_top, EReal.add_bot]
    exact bot_le
  -- both values are real
  lift f q₁ to ℝ using ⟨hf1, hf q₁⟩ with a ha
  lift g q₂ to ℝ using ⟨hg2, hg q₂⟩ with b hb
  -- apply the exchange with the sign-selected δ₁
  obtain ⟨δ₂, hδ₂, hkey⟩ := hQ q₁ q₂ (exDelta p p' q₁ q₂) (exDelta_mem p p' q₁ q₂)
  set d : Fin n → ℝ := exDelta p p' q₁ q₂ - δ₂ with hd
  rw [← ha, ← hb] at hkey
  -- the moved values are finite as well
  have hfd_ne_top : f (q₁ - d) ≠ ⊤ := by
    intro htop
    rw [htop, EReal.top_add_of_ne_bot (hg (q₂ + d)), ← EReal.coe_add] at hkey
    exact EReal.coe_ne_top (a + b) (top_le_iff.mp hkey)
  have hgd_ne_top : g (q₂ + d) ≠ ⊤ := by
    intro htop
    rw [htop, EReal.add_top_of_ne_bot (hf (q₁ - d)), ← EReal.coe_add] at hkey
    exact EReal.coe_ne_top (a + b) (top_le_iff.mp hkey)
  lift f (q₁ - d) to ℝ using ⟨hfd_ne_top, hf (q₁ - d)⟩ with a' ha'
  lift g (q₂ + d) to ℝ using ⟨hgd_ne_top, hg (q₂ + d)⟩ with b' hb'
  have hkey' : a' + b' ≤ a + b := by exact_mod_cast hkey
  -- lower-bound the two conjugates by the moved pair
  have hgle : (((q₂ + d) ⬝ᵥ p : ℝ) : EReal) - ((b' : ℝ) : EReal)
      ≤ fenchelConjugate n g p := by
    rw [fenchelConjugate_eq_iSup]
    have := le_iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ p : ℝ) : EReal) - g x) (q₂ + d)
    rwa [← hb'] at this
  have hfle : (((q₁ - d) ⬝ᵥ p' : ℝ) : EReal) - ((a' : ℝ) : EReal)
      ≤ fenchelConjugate n f p' := by
    rw [fenchelConjugate_eq_iSup]
    have := le_iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ p' : ℝ) : EReal) - f x) (q₁ - d)
    rwa [← ha'] at this
  refine le_trans ?_ (add_le_add hgle hfle)
  -- and close with the real dot-product inequality
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hdot := dotProduct_exchange_bound p p' q₁ q₂ δ₂ hδ₂
  rw [← hd] at hdot
  linarith

end GHS
