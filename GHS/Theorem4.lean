import GHS.PaschHausdorff

/-!
# GHS Theorem 4 packaged: ε-versions, Claim 1, and Corollary 1 (case `D = 𝒵`)

Roadmap items 12–14 at `D = 𝒵`:

* **Item 14 / Claim 1** — `qOrderE_iff_pOrderE_fenchelConjugate`: for closed
  proper convex `f, g`, `f ≤_Q g ⟺ g* ≤_P f*`.  This is the paper's
  Claim 1 = Theorem 4 at `D = 𝒵`, no `ε` (both directions from
  `GHS/Conjugacy.lean` and `GHS/PaschHausdorff.lean`).
* **Item 12 (ε-bridges)** — `QOrderEps`/`POrderEps` are the `ε`-refinements of
  Appendix A at `D = 𝒵`; `qOrderE_iff_forall_qOrderEps` and
  `pOrderE_iff_forall_pOrderEps` show they are equivalent to the plain orders
  (the Q-side bridge is the compactness argument the paper alludes to in its
  proof of (2)⟹(1); the P-side is elementary).  Together:
  `theorem4_eps` — `(∀ε>0, f ≤_{ε,Q} g) ⟺ (∀ε>0, g* ≤_{ε,P} f*)`.
* **Item 13 / Corollary 1** — `qOrderSet_iff_pOrderE_support`: for closed
  convex nonempty `X, Y`, `X ≤_Q Y ⟺ σ_Y ≤_P σ_X`, with the support
  function realized as `fenchelConjugate n (indER ·)`.

The general-`D` refinements (projections; needed for the *projected* forms of
Theorem 2 items (3)–(4)) are deferred — see the roadmap.

The complete statement now builds against Mathlib alone.
-/

open Set

namespace GHS

variable {n : ℕ}

/-! ## The ε-orders at `D = 𝒵` -/

/-- The `ε`-Q-order at `D = 𝒵` (GHS Appendix A, specialized). -/
def QOrderEps (ε : ℝ) (f g : (Fin n → ℝ) → EReal) : Prop :=
  ∀ q q' : Fin n → ℝ, f q ≠ ⊤ → g q' ≠ ⊤ →
    ∀ δ₁ ∈ Icc 0 ((q - q')⁺), ∃ δ₂ ∈ Icc 0 ((q - q')⁻),
      f (q - (δ₁ - δ₂)) + g (q' + (δ₁ - δ₂)) < f q + g q' + (ε : EReal)

/-- The `ε`-P-order at `D = 𝒵` (GHS Appendix A, specialized). -/
def POrderEps (ε : ℝ) (φ φ' : (Fin n → ℝ) → EReal) : Prop :=
  ∀ p p' : Fin n → ℝ, φ p ≠ ⊤ → φ' p' ≠ ⊤ →
    φ (p ⊓ p') + φ' (p ⊔ p') < φ p + φ' p' + (ε : EReal)

/-! ## Item 14: Claim 1 = Theorem 4, plain form -/

/-- **GHS Claim 1 / Theorem 4 at `D = 𝒵` (machine-verified equivalence).**
For closed proper convex `f, g` on `ℝⁿ`: `f ≤_Q g ⟺ g* ≤_P f*`. -/
theorem qOrderE_iff_pOrderE_fenchelConjugate {f g : (Fin n → ℝ) → EReal}
    (hf_lsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f)
    (hg_lsc : LowerSemicontinuous g) (hg : ProperConvexFunctionOn Set.univ g) :
    QOrderE f g ↔ POrderE (fenchelConjugate n g) (fenchelConjugate n f) :=
  ⟨pOrderE_fenchelConjugate_of_qOrderE (fun x => hf.2.2 x trivial)
      (fun x => hg.2.2 x trivial),
    qOrderE_of_pOrderE_fenchelConjugate hf_lsc hf hg_lsc hg⟩

/-! ## Item 12: the ε-bridges -/

/-- The plain Q-order gives every `ε`-Q-order (trivial direction). -/
theorem qOrderEps_of_qOrderE {f g : (Fin n → ℝ) → EReal}
    (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ x, g x ≠ ⊥)
    (h : QOrderE f g) {ε : ℝ} (hε : 0 < ε) : QOrderEps ε f g := by
  intro q q' hq hq' δ₁ hδ₁
  obtain ⟨δ₂, hδ₂, hkey⟩ := h q q' δ₁ hδ₁
  refine ⟨δ₂, hδ₂, lt_of_le_of_lt hkey ?_⟩
  lift f q to ℝ using ⟨hq, hfbot q⟩ with α hα
  lift g q' to ℝ using ⟨hq', hgbot q'⟩ with β hβ
  rw [← EReal.coe_add, ← EReal.coe_add]
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

/-- The `ε`-Q-orders for all `ε > 0` recover the plain Q-order: the
compactness bridge (GHS Appendix A, proof of (2)⟹(1)). -/
theorem qOrderE_of_forall_qOrderEps {f g : (Fin n → ℝ) → EReal}
    (hf_lsc : LowerSemicontinuous f) (hg_lsc : LowerSemicontinuous g)
    (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ x, g x ≠ ⊥)
    (h : ∀ ε : ℝ, 0 < ε → QOrderEps ε f g) : QOrderE f g := by
  intro q₁ q₂ δ₁ hδ₁
  by_cases hfq : f q₁ = ⊤
  · refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
    rw [hfq, EReal.top_add_of_ne_bot (hgbot q₂)]
    exact le_top
  by_cases hgq : g q₂ = ⊤
  · refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
    rw [hgq, EReal.add_top_of_ne_bot (hfbot q₁)]
    exact le_top
  lift f q₁ to ℝ using ⟨hfq, hfbot q₁⟩ with α hα
  lift g q₂ to ℝ using ⟨hgq, hgbot q₂⟩ with β hβ
  have hfq' : f q₁ ≠ ⊤ := by rw [← hα]; exact EReal.coe_ne_top α
  have hgq' : g q₂ ≠ ⊤ := by rw [← hβ]; exact EReal.coe_ne_top β
  have hex : ∀ k : ℕ, ∃ δ₂ ∈ Icc 0 ((q₁ - q₂)⁻),
      f (q₁ - (δ₁ - δ₂)) + g (q₂ + (δ₁ - δ₂))
        < ((α + β + 1 / (k + 1) : ℝ) : EReal) := by
    intro k
    have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
    obtain ⟨δ₂, hδ₂, hkey⟩ := h _ hpos q₁ q₂ hfq' hgq' δ₁ hδ₁
    refine ⟨δ₂, hδ₂, ?_⟩
    rw [← hα, ← hβ] at hkey
    rwa [← EReal.coe_add, ← EReal.coe_add] at hkey
  classical
  choose δs hδs_mem hδs_key using hex
  obtain ⟨δstar, hmem, ψ, hψmono, hψtend⟩ :=
    (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := (q₁ - q₂)⁻)).tendsto_subseq hδs_mem
  refine ⟨δstar, hmem, ?_⟩
  refine EReal.add_le_of_forall_lt fun y hy z hz => ?_
  have hopen1 : IsOpen {x : Fin n → ℝ | y < f x} :=
    lowerSemicontinuous_iff_isOpen_preimage.mp hf_lsc y
  have hopen2 : IsOpen {x : Fin n → ℝ | z < g x} :=
    lowerSemicontinuous_iff_isOpen_preimage.mp hg_lsc z
  have htend_a : Filter.Tendsto (fun k => q₁ - (δ₁ - δs (ψ k))) Filter.atTop
      (nhds (q₁ - (δ₁ - δstar))) := by
    have hcont : Continuous (fun x : Fin n → ℝ => q₁ - (δ₁ - x)) :=
      continuous_const.sub (continuous_const.sub continuous_id)
    exact (hcont.tendsto δstar).comp hψtend
  have htend_b : Filter.Tendsto (fun k => q₂ + (δ₁ - δs (ψ k))) Filter.atTop
      (nhds (q₂ + (δ₁ - δstar))) := by
    have hcont : Continuous (fun x : Fin n → ℝ => q₂ + (δ₁ - x)) :=
      continuous_const.add (continuous_const.sub continuous_id)
    exact (hcont.tendsto δstar).comp hψtend
  have hev1 : ∀ᶠ k in Filter.atTop, y < f (q₁ - (δ₁ - δs (ψ k))) :=
    htend_a.eventually (hopen1.mem_nhds hy)
  have hev2 : ∀ᶠ k in Filter.atTop, z < g (q₂ + (δ₁ - δs (ψ k))) :=
    htend_b.eventually (hopen2.mem_nhds hz)
  -- reduce to real y, z (⊥ is trivial; ⊤ is impossible)
  rcases eq_or_ne y ⊥ with rfl | hybot
  · rw [EReal.bot_add]
    exact bot_le
  rcases eq_or_ne z ⊥ with rfl | hzbot
  · rw [EReal.add_bot]
    exact bot_le
  have hytop : y ≠ ⊤ := fun htop => absurd (htop ▸ hy) (by simp)
  have hztop : z ≠ ⊤ := fun htop => absurd (htop ▸ hz) (by simp)
  lift y to ℝ using ⟨hytop, hybot⟩ with yr hyr
  lift z to ℝ using ⟨hztop, hzbot⟩ with zr hzr
  rw [← EReal.coe_add, ← EReal.coe_add]
  refine EReal.coe_le_coe_iff.mpr ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt (show (0:ℝ) < yr + zr - (α + β) by linarith)
  obtain ⟨k, hk1, hk2, hk3⟩ :=
    (hev1.and (hev2.and (Filter.eventually_ge_atTop k₀))).exists
  have hchain : ((yr + zr : ℝ) : EReal)
      < ((α + β + 1 / (ψ k + 1) : ℝ) : EReal) := by
    calc ((yr + zr : ℝ) : EReal) = ((yr : ℝ) : EReal) + ((zr : ℝ) : EReal) :=
          EReal.coe_add _ _
      _ ≤ f (q₁ - (δ₁ - δs (ψ k))) + g (q₂ + (δ₁ - δs (ψ k))) :=
          add_le_add hk1.le hk2.le
      _ < _ := hδs_key (ψ k)
  have hreal : yr + zr < α + β + 1 / (ψ k + 1) := EReal.coe_lt_coe_iff.mp hchain
  have hmono : 1 / ((ψ k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    have h1 : (k : ℝ) + 1 ≤ (ψ k : ℝ) + 1 := by
      have h2 : k ≤ ψ k := hψmono.le_apply
      exact_mod_cast Nat.succ_le_succ h2
    exact one_div_le_one_div_of_le (by positivity) h1
  have hk₀' : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) := by
    have h1 : (k₀ : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk3
    exact one_div_le_one_div_of_le (by positivity) h1
  linarith [hk₀, hmono, hk₀', hreal]

/-- The plain P-order gives every `ε`-P-order (trivial direction). -/
theorem pOrderEps_of_pOrderE {φ φ' : (Fin n → ℝ) → EReal}
    (hφbot : ∀ x, φ x ≠ ⊥) (hφ'bot : ∀ x, φ' x ≠ ⊥)
    (h : POrderE φ φ') {ε : ℝ} (hε : 0 < ε) : POrderEps ε φ φ' := by
  intro p p' hp hp'
  refine lt_of_le_of_lt (h p p') ?_
  lift φ p to ℝ using ⟨hp, hφbot p⟩ with α hα
  lift φ' p' to ℝ using ⟨hp', hφ'bot p'⟩ with β hβ
  rw [← EReal.coe_add, ← EReal.coe_add]
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

/-- The `ε`-P-orders for all `ε > 0` recover the plain P-order (elementary). -/
theorem pOrderE_of_forall_pOrderEps {φ φ' : (Fin n → ℝ) → EReal}
    (hφbot : ∀ x, φ x ≠ ⊥) (hφ'bot : ∀ x, φ' x ≠ ⊥)
    (h : ∀ ε : ℝ, 0 < ε → POrderEps ε φ φ') : POrderE φ φ' := by
  intro p p'
  by_cases hp : φ p = ⊤
  · rw [hp, EReal.top_add_of_ne_bot (hφ'bot p')]
    exact le_top
  by_cases hp' : φ' p' = ⊤
  · rw [hp', EReal.add_top_of_ne_bot (hφbot p)]
    exact le_top
  lift φ p to ℝ using ⟨hp, hφbot p⟩ with α hα
  lift φ' p' to ℝ using ⟨hp', hφ'bot p'⟩ with β hβ
  have hp2 : φ p ≠ ⊤ := by rw [← hα]; exact EReal.coe_ne_top α
  have hp2' : φ' p' ≠ ⊤ := by rw [← hβ]; exact EReal.coe_ne_top β
  set A : EReal := φ (p ⊓ p') + φ' (p ⊔ p') with hA
  by_contra hlt
  push_neg at hlt
  have hstep := h 1 one_pos p p' hp2 hp2'
  rw [← hα, ← hβ, ← hA] at hstep
  have hAtop : A ≠ ⊤ := (lt_of_lt_of_le hstep le_top).ne
  have hAbot : A ≠ ⊥ := by
    intro hbot
    rw [hbot] at hlt
    exact absurd hlt (by simp)
  lift A to ℝ using ⟨hAtop, hAbot⟩ with γ hγ
  have hlt' : α + β < γ := by
    rw [← EReal.coe_add] at hlt
    exact EReal.coe_lt_coe_iff.mp hlt
  have hstep2 := h ((γ - (α + β)) / 2) (by linarith) p p' hp2 hp2'
  rw [← hα, ← hβ, ← hA, ← EReal.coe_add, ← EReal.coe_add] at hstep2
  have := EReal.coe_lt_coe_iff.mp hstep2
  linarith

/-- **Theorem 4 at `D = 𝒵`, ε-form**: the ε-Q-orders hold for every `ε > 0`
iff the ε-P-orders of the conjugates do. -/
theorem theorem4_eps {f g : (Fin n → ℝ) → EReal}
    (hf_lsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f)
    (hg_lsc : LowerSemicontinuous g) (hg : ProperConvexFunctionOn Set.univ g) :
    (∀ ε : ℝ, 0 < ε → QOrderEps ε f g) ↔
      (∀ ε : ℝ, 0 < ε → POrderEps ε (fenchelConjugate n g) (fenchelConjugate n f)) := by
  have hfbot : ∀ x, f x ≠ ⊥ := fun x => hf.2.2 x trivial
  have hgbot : ∀ x, g x ≠ ⊥ := fun x => hg.2.2 x trivial
  constructor
  · intro h ε hε
    refine pOrderEps_of_pOrderE (fenchelConjugate_ne_bot hg) (fenchelConjugate_ne_bot hf)
      ((qOrderE_iff_pOrderE_fenchelConjugate hf_lsc hf hg_lsc hg).mp ?_) hε
    exact qOrderE_of_forall_qOrderEps hf_lsc hg_lsc hfbot hgbot h
  · intro h ε hε
    refine qOrderEps_of_qOrderE hfbot hgbot ?_ hε
    refine (qOrderE_iff_pOrderE_fenchelConjugate hf_lsc hf hg_lsc hg).mpr ?_
    exact pOrderE_of_forall_pOrderEps (fenchelConjugate_ne_bot hg)
      (fenchelConjugate_ne_bot hf) h

/-! ## Item 13: Corollary 1 — the set version via support functions -/

/-- The indicator of a closed convex nonempty set is proper convex. -/
theorem properConvexOn_indER {X : Set (Fin n → ℝ)} (hXc : Convex ℝ X)
    (hXne : X.Nonempty) : ProperConvexFunctionOn Set.univ (indER X) := by
  obtain ⟨x₀, hx₀⟩ := hXne
  refine ⟨?_, ⟨(x₀, 0), trivial, ?_⟩, fun u _ => ?_⟩
  · show Convex ℝ (epigraph Set.univ (indER X))
    have hset : epigraph (Set.univ : Set (Fin n → ℝ)) (indER X)
        = X ×ˢ (Ici (0 : ℝ)) := by
      ext p
      constructor
      · rintro ⟨-, h⟩
        by_cases hp : p.1 ∈ X
        · rw [show indER X p.1 = 0 from if_pos hp] at h
          exact ⟨hp, by exact_mod_cast h⟩
        · rw [show indER X p.1 = ⊤ from if_neg hp] at h
          exact absurd (top_le_iff.mp h) (EReal.coe_ne_top p.2)
      · rintro ⟨hmem, h⟩
        refine ⟨trivial, ?_⟩
        rw [show indER X p.1 = 0 from if_pos hmem]
        exact_mod_cast h
    rw [hset]
    exact hXc.prod (convex_Ici _)
  · show indER X x₀ ≤ (((0 : ℝ)) : EReal)
    rw [show indER X x₀ = 0 from if_pos hx₀]
    exact_mod_cast le_refl (0 : ℝ)
  · show indER X u ≠ ⊥
    unfold indER
    split <;> simp

/-- The set Q-order coincides with the function Q-order of the indicators. -/
theorem qOrderE_indER_iff {X Y : Set (Fin n → ℝ)} :
    QOrderE (indER X) (indER Y) ↔ QOrderSet X Y := by
  constructor
  · intro h x hx y hy δ₁ hδ₁
    obtain ⟨δ₂, hδ₂, hkey⟩ := h x y δ₁ hδ₁
    rw [show indER X x = 0 from if_pos hx, show indER Y y = 0 from if_pos hy,
      add_zero] at hkey
    refine ⟨δ₂, hδ₂, ?_, ?_⟩
    · by_contra hmem
      rw [show indER X (x - (δ₁ - δ₂)) = ⊤ from if_neg hmem,
        EReal.top_add_of_ne_bot (by unfold indER; split <;> simp)] at hkey
      exact absurd hkey (by simp)
    · by_contra hmem
      rw [show indER Y (y + (δ₁ - δ₂)) = ⊤ from if_neg hmem,
        EReal.add_top_of_ne_bot (by unfold indER; split <;> simp)] at hkey
      exact absurd hkey (by simp)
  · intro h q q' δ₁ hδ₁
    by_cases hq : q ∈ X
    · by_cases hq' : q' ∈ Y
      · obtain ⟨δ₂, hδ₂, h1, h2⟩ := h q hq q' hq' δ₁ hδ₁
        refine ⟨δ₂, hδ₂, ?_⟩
        rw [show indER X q = 0 from if_pos hq, show indER Y q' = 0 from if_pos hq',
          show indER X (q - (δ₁ - δ₂)) = 0 from if_pos h1,
          show indER Y (q' + (δ₁ - δ₂)) = 0 from if_pos h2]
      · refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
        rw [show indER Y q' = ⊤ from if_neg hq',
          EReal.add_top_of_ne_bot (by unfold indER; split <;> simp)]
        exact le_top
    · refine ⟨0, ⟨le_refl 0, negPart_nonneg _⟩, ?_⟩
      rw [show indER X q = ⊤ from if_neg hq,
        EReal.top_add_of_ne_bot (by unfold indER; split <;> simp)]
      exact le_top

/-- **GHS Corollary 1 at `D = 𝒵`.** For closed convex nonempty `X, Y`:
`X ≤_Q Y ⟺ σ_Y ≤_P σ_X`, where the support function is realized as the
Fenchel conjugate of the indicator. -/
theorem qOrderSet_iff_pOrderE_support {X Y : Set (Fin n → ℝ)}
    (hX : IsClosed X) (hXc : Convex ℝ X) (hXne : X.Nonempty)
    (hY : IsClosed Y) (hYc : Convex ℝ Y) (hYne : Y.Nonempty) :
    QOrderSet X Y ↔
      POrderE (fenchelConjugate n (indER Y)) (fenchelConjugate n (indER X)) := by
  rw [← qOrderE_indER_iff]
  exact qOrderE_iff_pOrderE_fenchelConjugate
    (lowerSemicontinuous_indER hX) (properConvexOn_indER hXc hXne)
    (lowerSemicontinuous_indER hY) (properConvexOn_indER hYc hYne)

end GHS
