import GHS.Theorem4

/-!
# General-D epsilon conjugacy

This file formalizes the projected `(epsilon, D)` orders from the submitted
GHS appendix on the `EReal` side.  The first theorem proves the elementary
conjugacy direction with explicit slack: a Q comparison with slack `epsilon / 2`
implies the conjugate P comparison with slack `epsilon`.
-/

open Set

namespace GHS

variable {n : ℕ}

/-- The `(epsilon, D)` Q-order for `EReal`-valued functions. -/
def QOrderEpsD (ε : ℝ) (D : Set (Fin n))
    (f g : (Fin n → ℝ) → EReal) : Prop :=
  ∀ x y, f x ≠ ⊤ → g y ≠ ⊤ →
    ∀ δ₁ ∈ Icc 0 ((x - y)⁺), (∀ i ∉ D, δ₁ i = 0) →
      ∃ δ₂, (∀ i ∈ D, δ₂ i ∈ Icc 0 ((x - y)⁻ i)) ∧
        f (x - δ₁ + δ₂) + g (y + δ₁ - δ₂) < f x + g y + (ε : EReal)

/-- The `(epsilon, D)` P-order for `EReal`-valued functions. -/
def POrderEpsD (ε : ℝ) (D : Set (Fin n))
    (φ φ' : (Fin n → ℝ) → EReal) : Prop :=
  ∀ lam pf pg, (∀ i ∉ D, pf i = 0) → (∀ i ∉ D, pg i = 0) →
    φ (lam + pf) ≠ ⊤ → φ' (lam + pg) ≠ ⊤ →
      φ (lam + (pf ⊓ pg)) + φ' (lam + (pf ⊔ pg))
        < φ (lam + pf) + φ' (lam + pg) + (ε : EReal)

/-- If `pf` and `pg` vanish off `D`, the sign-selected exchange also vanishes
off `D`. -/
theorem exDelta_support_of_support {D : Set (Fin n)}
    {pf pg q₁ q₂ : Fin n → ℝ}
    (hpf : ∀ i ∉ D, pf i = 0) (hpg : ∀ i ∉ D, pg i = 0) :
    ∀ i ∉ D, exDelta pf pg q₁ q₂ i = 0 := by
  intro i hi
  simp [exDelta, hpf i hi, hpg i hi]

/-- The exchange dot-product estimate when the two prices agree off `D` and
the reverse exchange is constrained only on `D`. -/
theorem dotProduct_exchange_bound_D {D : Set (Fin n)}
    (p p' q₁ q₂ δ₂ : Fin n → ℝ)
    (hpp' : ∀ i ∉ D, p i = p' i)
    (hδ₂ : ∀ i ∈ D, δ₂ i ∈ Icc 0 ((q₁ - q₂)⁻ i)) :
    q₂ ⬝ᵥ (p ⊓ p') + q₁ ⬝ᵥ (p ⊔ p')
      ≤ (q₂ + (exDelta p p' q₁ q₂ - δ₂)) ⬝ᵥ p
        + (q₁ - (exDelta p p' q₁ q₂ - δ₂)) ⬝ᵥ p' := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ D
  · have h := coord_exchange (p i) (p' i) (q₁ i) (q₂ i) (δ₂ i)
      (hδ₂ i hi).1 (hδ₂ i hi).2
    simpa [exDelta, Pi.add_apply, Pi.sub_apply, Pi.inf_apply, Pi.sup_apply] using h
  · have heq := hpp' i hi
    simp [exDelta, heq, Pi.add_apply, Pi.sub_apply, Pi.inf_apply, Pi.sup_apply]
    ring_nf
    exact le_rfl

/-- General-`D` conjugacy, elementary direction with slack.  A Q comparison
with slack `epsilon / 2` implies the P comparison of the conjugates with slack
`epsilon`. -/
theorem pOrderEpsD_fenchelConjugate_of_qOrderEpsD
    {D : Set (Fin n)} {f g : (Fin n → ℝ) → EReal} {ε : ℝ}
    (hε : 0 < ε) (hf : ProperConvexFunctionOn Set.univ f)
    (hg : ProperConvexFunctionOn Set.univ g)
    (hQ : QOrderEpsD (ε / 2) D f g) :
    POrderEpsD ε D (fenchelConjugate n g) (fenchelConjugate n f) := by
  have hfbot : ∀ x, f x ≠ ⊥ := fun x => hf.2.2 x trivial
  have hgbot : ∀ x, g x ≠ ⊥ := fun x => hg.2.2 x trivial
  intro lam pf pg hpf hpg hcg hcf
  let p : Fin n → ℝ := lam + pf
  let p' : Fin n → ℝ := lam + pg
  have hpp' : ∀ i ∉ D, p i = p' i := by
    intro i hi
    simp [p, p', hpf i hi, hpg i hi]
  have hmin : p ⊓ p' = lam + (pf ⊓ pg) := by
    ext i
    simp [p, p', min_add_add_left]
  have hmax : p ⊔ p' = lam + (pf ⊔ pg) := by
    ext i
    simp [p, p', max_add_add_left]
  lift fenchelConjugate n g p to ℝ using
    ⟨show fenchelConjugate n g p ≠ ⊤ by simpa [p] using hcg,
      fenchelConjugate_ne_bot hg p⟩ with A hA
  lift fenchelConjugate n f p' to ℝ using
    ⟨show fenchelConjugate n f p' ≠ ⊤ by simpa [p'] using hcf,
      fenchelConjugate_ne_bot hf p'⟩ with B hB
  rw [← hmin, ← hmax]
  change fenchelConjugate n g (p ⊓ p') + fenchelConjugate n f (p ⊔ p') <
    fenchelConjugate n g p + fenchelConjugate n f p' + (ε : EReal)
  rw [fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup,
    section16_iSup_add_iSup_eq_iSup_prod]
  refine lt_of_le_of_lt
    (b := fenchelConjugate n g p + fenchelConjugate n f p' + ((ε / 2 : ℝ) : EReal))
    (iSup_le fun z => ?_) ?_
  obtain ⟨q₂, q₁⟩ := z
  show (((q₂ ⬝ᵥ (p ⊓ p') : ℝ) : EReal) - g q₂) +
      (((q₁ ⬝ᵥ (p ⊔ p') : ℝ) : EReal) - f q₁)
      ≤ fenchelConjugate n g p + fenchelConjugate n f p' + ((ε / 2 : ℝ) : EReal)
  by_cases hg2 : g q₂ = ⊤
  · rw [hg2, EReal.sub_top, EReal.bot_add]
    exact bot_le
  by_cases hf1 : f q₁ = ⊤
  · rw [hf1, EReal.sub_top, EReal.add_bot]
    exact bot_le
  let δ₁ := exDelta p p' q₁ q₂
  have hδ₁ : δ₁ ∈ Icc 0 ((q₁ - q₂)⁺) := exDelta_mem p p' q₁ q₂
  have hδ₁D : ∀ i ∉ D, δ₁ i = 0 := by
    intro i hi
    simp [δ₁, exDelta, hpp' i hi]
  obtain ⟨δ₂, hδ₂, hkey⟩ := hQ q₁ q₂ hf1 hg2 δ₁ hδ₁ hδ₁D
  lift f q₁ to ℝ using ⟨hf1, hfbot q₁⟩ with a ha
  lift g q₂ to ℝ using ⟨hg2, hgbot q₂⟩ with b hb
  let d := δ₁ - δ₂
  have hfd_ne_top : f (q₁ - δ₁ + δ₂) ≠ ⊤ := by
    intro ht
    rw [ht, EReal.top_add_of_ne_bot (hgbot _), ← EReal.coe_add, ← EReal.coe_add] at hkey
    exact (EReal.coe_ne_top (a + b + ε / 2)) (top_le_iff.mp hkey.le)
  have hgd_ne_top : g (q₂ + δ₁ - δ₂) ≠ ⊤ := by
    intro ht
    rw [ht, EReal.add_top_of_ne_bot (hfbot _), ← EReal.coe_add, ← EReal.coe_add] at hkey
    exact (EReal.coe_ne_top (a + b + ε / 2)) (top_le_iff.mp hkey.le)
  lift f (q₁ - δ₁ + δ₂) to ℝ using ⟨hfd_ne_top, hfbot _⟩ with a' ha'
  lift g (q₂ + δ₁ - δ₂) to ℝ using ⟨hgd_ne_top, hgbot _⟩ with b' hb'
  have hkey' : a' + b' < a + b + ε / 2 := by
    exact_mod_cast hkey
  have hgle : ((((q₂ + d) ⬝ᵥ p : ℝ) : EReal) - (b' : EReal))
      ≤ fenchelConjugate n g p := by
    rw [fenchelConjugate_eq_iSup]
    have heq : q₂ + d = q₂ + δ₁ - δ₂ := by
      ext i
      simp [d]
      ring
    rw [heq]
    simpa only [← hb'] using
      (le_iSup (fun x => ((x ⬝ᵥ p : ℝ) : EReal) - g x) (q₂ + δ₁ - δ₂))
  have hfle : ((((q₁ - d) ⬝ᵥ p' : ℝ) : EReal) - (a' : EReal))
      ≤ fenchelConjugate n f p' := by
    rw [fenchelConjugate_eq_iSup]
    have heq : q₁ - d = q₁ - δ₁ + δ₂ := by
      ext i
      simp [d]
      ring
    rw [heq]
    simpa only [← ha'] using
      (le_iSup (fun x => ((x ⬝ᵥ p' : ℝ) : EReal) - f x) (q₁ - δ₁ + δ₂))
  refine le_trans ?_ (add_le_add (add_le_add hgle hfle) le_rfl)
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hdot := dotProduct_exchange_bound_D p p' q₁ q₂ δ₂ hpp' hδ₂
  change (q₂ ⬝ᵥ (p ⊓ p') - b) + (q₁ ⬝ᵥ (p ⊔ p') - a) ≤
    ((q₂ + d) ⬝ᵥ p - b') + ((q₁ - d) ⬝ᵥ p' - a') + ε / 2
  linarith
  rw [← hA, ← hB, ← EReal.coe_add, ← EReal.coe_add]
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

/-- General-`D` conjugacy, elementary direction in the robust epsilon form.
If every positive-slack Q comparison holds, then every positive-slack P
comparison of the conjugates holds. -/
theorem forall_pOrderEpsD_fenchelConjugate_of_forall_qOrderEpsD
    {D : Set (Fin n)} {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn Set.univ f)
    (hg : ProperConvexFunctionOn Set.univ g)
    (hQ : ∀ ε : ℝ, 0 < ε → QOrderEpsD ε D f g) :
    ∀ ε : ℝ, 0 < ε →
      POrderEpsD ε D (fenchelConjugate n g) (fenchelConjugate n f) := by
  intro ε hε
  exact pOrderEpsD_fenchelConjugate_of_qOrderEpsD hε hf hg
    (hQ (ε / 2) (by linarith))

end GHS
