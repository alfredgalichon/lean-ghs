import GHS.ConjugacyDual

/-!
# GHS Phase 4 (item 11, completed): P ⟹ Q in full generality

`GHS.qOrderE_of_pOrderE_fenchelConjugate` extends the finite-valued case of
`GHS/ConjugacyDual.lean` to arbitrary **closed proper convex** `f, g`:
if `g* ≤_P f*` then `f ≤_Q g`.  Together with
`GHS.pOrderE_fenchelConjugate_of_qOrderE` this completes GHS **Theorem 4**
(case `D = 𝒵`, no `ε`) as a machine-verified equivalence.

The regularization is Pasch–Hausdorff seen from the dual side: for `L : ℕ`
set `φ_L := f* + ι_{[-L,L]ⁿ}` (`restrictCube`) and `f_L := (φ_L)*`.  Then:

* `f_L` is finite-valued for large `L` (a Fenchel–Young bound above, a point
  of `dom f* ∩ [-L,L]ⁿ` below) and convex, so the finite-valued theorem
  applies to the pair `(f_L, g_L)`;
* `(f_L)* = φ_L` by the local finite-dimensional Fenchel–Moreau theorem, and
  the P-order passes from `(g*, f*)` to
  `(ψ_L, φ_L)` because the cube is a sublattice on which the indicators are
  modular (`pOrderE_restrictCube`);
* the exchange witnesses `δ₂^L` live in the compact box `[0, (q₁-q₂)⁻]`; a
  convergent subsequence produces the witness for `(f, g)`.  The limit
  inequality needs no liminf calculus: for any reals `y < f(a*)`, `z < g(b*)`,
  biconjugation writes `f(a*)` as a supremum over dual points, each dual point
  lies in some cube, so `y < f_M(a*)` for some `M`; lower semicontinuity of
  `f_M` (a conjugate) makes `{f_M > y}` open, and along the subsequence
  `y + z < f_{L_k}(a_k) + g_{L_k}(b_k) ≤ f q₁ + g q₂` eventually.  Conclude
  with `EReal.add_le_of_forall_lt`.

This file depends only on Mathlib and the local `GHS.Rockafellar` layer.
-/

open Set

namespace GHS

variable {n : ℕ}

/-! ## The cube and the restricted conjugate -/

/-- The coordinate cube `[-L, L]ⁿ`. -/
def cube (L : ℝ) : Set (Fin n → ℝ) := Icc (fun _ => -L) (fun _ => L)

theorem cube_mono {L L' : ℝ} (h : L ≤ L') : cube (n := n) L ⊆ cube L' := by
  rintro u ⟨h1, h2⟩
  exact ⟨fun i => le_trans (by simpa using neg_le_neg h) (h1 i),
    fun i => le_trans (h2 i) (by simpa using h)⟩

theorem mem_cube_iff {L : ℝ} {u : Fin n → ℝ} :
    u ∈ cube (n := n) L ↔ ∀ i, |u i| ≤ L := by
  constructor
  · rintro ⟨h1, h2⟩ i
    exact abs_le.mpr ⟨by simpa using h1 i, h2 i⟩
  · intro h
    exact ⟨fun i => by simpa using (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩

theorem dotProduct_le_of_mem_cube {L : ℝ} {u : Fin n → ℝ}
    (hu : u ∈ cube (n := n) L) (w : Fin n → ℝ) :
    u ⬝ᵥ w ≤ L * ∑ i, |w i| := by
  rw [Finset.mul_sum]
  simp only [dotProduct]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : |u i| ≤ L := mem_cube_iff.mp hu i
  calc u i * w i ≤ |u i * w i| := le_abs_self _
    _ = |u i| * |w i| := abs_mul _ _
    _ ≤ L * |w i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

theorem indER_nonneg (S : Set (Fin n → ℝ)) (u : Fin n → ℝ) : 0 ≤ indER S u := by
  unfold indER
  split
  · exact le_refl _
  · exact le_top

/-- The dual-side Pasch–Hausdorff operation: restrict a conjugate to a cube. -/
noncomputable def restrictCube (L : ℝ) (φ : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun u => φ u + indER (cube L) u

theorem le_restrictCube (L : ℝ) (φ : (Fin n → ℝ) → EReal) :
    φ ≤ restrictCube L φ :=
  fun u => le_add_of_nonneg_right (indER_nonneg _ u)

theorem restrictCube_antitone {L L' : ℝ} (h : L ≤ L') (φ : (Fin n → ℝ) → EReal) :
    restrictCube L' φ ≤ restrictCube L φ := by
  intro u
  refine add_le_add (le_refl _) ?_
  by_cases hu : u ∈ cube (n := n) L
  · rw [show indER (cube (n := n) L) u = 0 from if_pos hu,
      show indER (cube (n := n) L') u = 0 from if_pos (cube_mono h hu)]
  · rw [show indER (cube (n := n) L) u = ⊤ from if_neg hu]
    exact le_top

theorem restrictCube_of_mem {L : ℝ} {u : Fin n → ℝ} (hu : u ∈ cube (n := n) L)
    (φ : (Fin n → ℝ) → EReal) : restrictCube L φ u = φ u := by
  rw [restrictCube, show indER (cube (n := n) L) u = 0 from if_pos hu, add_zero]

theorem restrictCube_of_not_mem {L : ℝ} {u : Fin n → ℝ} (hu : u ∉ cube (n := n) L)
    {φ : (Fin n → ℝ) → EReal} (hφ : φ u ≠ ⊥) : restrictCube L φ u = ⊤ := by
  rw [restrictCube, show indER (cube (n := n) L) u = ⊤ from if_neg hu]
  exact EReal.add_top_of_ne_bot hφ

/-! ## Generalities on conjugates of proper functions -/

/-- Fenchel–Young: any point of the domain bounds the conjugate from below. -/
theorem coe_sub_le_fenchelConjugate (f : (Fin n → ℝ) → EReal) (q₀ u : Fin n → ℝ) :
    ((q₀ ⬝ᵥ u : ℝ) : EReal) - f q₀ ≤ fenchelConjugate n f u := by
  rw [fenchelConjugate_eq_iSup]
  exact le_iSup (fun x => ((x ⬝ᵥ u : ℝ) : EReal) - f x) q₀

/-- The conjugate of a proper function never takes `⊥`. -/
theorem fenchelConjugate_ne_bot {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn Set.univ f) (u : Fin n → ℝ) :
    fenchelConjugate n f u ≠ ⊥ := by
  obtain ⟨p, hp1, hp2⟩ := hf.2.1
  have htop : f p.1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top p.2) hp2
  have hbot : f p.1 ≠ ⊥ := hf.2.2 p.1 trivial
  intro hzero
  have hle := coe_sub_le_fenchelConjugate f p.1 u
  rw [hzero] at hle
  lift f p.1 to ℝ using ⟨htop, hbot⟩ with r hr
  rw [← EReal.coe_sub] at hle
  exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)

/-- Biconjugation restores a closed proper convex function. -/
theorem fenchelConjugate_fenchelConjugate_eq {f : (Fin n → ℝ) → EReal}
    (hlsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f) :
    fenchelConjugate n (fenchelConjugate n f) = f := by
  exact fenchelConjugate_biconjugate hlsc hf

/-- The conjugate of a proper convex function has a point in its domain. -/
theorem exists_fenchelConjugate_ne_top {f : (Fin n → ℝ) → EReal}
    (hlsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f) :
    ∃ u, fenchelConjugate n f u ≠ ⊤ := by
  have hproper : ProperConvexFunctionOn Set.univ (fenchelConjugate n f) :=
    fenchelConjugate_proper hlsc hf
  obtain ⟨p, _, hp2⟩ := hproper.2.1
  exact ⟨p.1, ne_top_of_le_ne_top (EReal.coe_ne_top p.2) hp2⟩

/-! ## Lower semicontinuity and properness of the restricted conjugate -/

theorem lowerSemicontinuous_indER {S : Set (Fin n → ℝ)} (hS : IsClosed S) :
    LowerSemicontinuous (indER S) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  rcases le_or_gt (0 : EReal) y with hy | hy
  · rcases eq_or_ne y ⊤ with rfl | hytop
    · have h : indER S ⁻¹' Iic (⊤ : EReal) = Set.univ := by
        ext x
        simp
      rw [h]
      exact isClosed_univ
    · have h : indER S ⁻¹' Iic y = S := by
        ext x
        constructor
        · intro hx
          by_contra hxS
          have : indER S x = ⊤ := if_neg hxS
          rw [Set.mem_preimage, Set.mem_Iic, this] at hx
          exact hytop (top_le_iff.mp hx)
        · intro hxS
          rw [Set.mem_preimage, Set.mem_Iic, show indER S x = 0 from if_pos hxS]
          exact hy
      rw [h]
      exact hS
  · have h : indER S ⁻¹' Iic y = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      intro hx
      have h0 : (0 : EReal) ≤ indER S x := indER_nonneg S x
      exact absurd (le_trans h0 hx) (not_le.mpr hy)
    rw [h]
    exact isClosed_empty

theorem lowerSemicontinuous_restrictCube {φ : (Fin n → ℝ) → EReal} (L : ℝ)
    (hφ : LowerSemicontinuous φ) (hφbot : ∀ u, φ u ≠ ⊥) :
    LowerSemicontinuous (restrictCube L φ) := by
  refine hφ.add' (lowerSemicontinuous_indER (isClosed_Icc)) fun x => ?_
  refine EReal.continuousAt_add (Or.inr ?_) (Or.inl (hφbot x))
  show indER (cube L) x ≠ ⊥
  intro h
  have h0 := indER_nonneg (cube (n := n) L) x
  rw [h] at h0
  exact absurd h0 (by simp)

/-- Properness of the restricted conjugate, given a domain point in the cube. -/
theorem properConvexOn_restrictCube {φ : (Fin n → ℝ) → EReal} {L : ℝ}
    (hφ : ProperConvexFunctionOn Set.univ φ)
    (u₀ : Fin n → ℝ) (hu₀ : u₀ ∈ cube (n := n) L) (hu₀top : φ u₀ ≠ ⊤) :
    ProperConvexFunctionOn Set.univ (restrictCube L φ) := by
  have hφbot : ∀ u, φ u ≠ ⊥ := fun u => hφ.2.2 u trivial
  refine ⟨?_, ?_, fun u _ => ?_⟩
  · -- convexity: the epigraph is the intersection with the cube cylinder
    show Convex ℝ (epigraph Set.univ (restrictCube L φ))
    have hset : epigraph Set.univ (restrictCube L φ)
        = epigraph Set.univ φ ∩ ((cube L) ×ˢ (Set.univ : Set ℝ)) := by
      ext p
      constructor
      · rintro ⟨-, h⟩
        by_cases hp : p.1 ∈ cube (n := n) L
        · rw [restrictCube_of_mem hp] at h
          exact ⟨⟨trivial, h⟩, hp, trivial⟩
        · rw [restrictCube_of_not_mem hp (hφbot p.1)] at h
          exact absurd (top_le_iff.mp h) (EReal.coe_ne_top p.2)
      · rintro ⟨⟨-, h⟩, hp, -⟩
        exact ⟨trivial, by rw [restrictCube_of_mem hp]; exact h⟩
    rw [hset]
    exact hφ.1.inter ((convex_Icc _ _).prod convex_univ)
  · -- nonempty epigraph
    lift φ u₀ to ℝ using ⟨hu₀top, hφbot u₀⟩ with r hr
    refine ⟨(u₀, r), trivial, ?_⟩
    rw [restrictCube_of_mem hu₀, ← hr]
  · -- never ⊥
    intro h
    by_cases hu : u ∈ cube (n := n) L
    · rw [restrictCube_of_mem hu] at h
      exact hφbot u h
    · rw [restrictCube_of_not_mem hu (hφbot u)] at h
      exact absurd h (by simp)

/-! ## Finiteness of the regularized function -/

/-- The regularized function is nowhere `⊥` (bound above by Fenchel–Young at a
domain point of the primal). -/
theorem regularized_ne_top {f : (Fin n → ℝ) → EReal} {L : ℝ}
    (hf : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ) :
    fenchelConjugate n (restrictCube L (fenchelConjugate n f)) x ≠ ⊤ := by
  obtain ⟨p, hp1, hp2⟩ := hf.2.1
  have hftop : f p.1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top p.2) hp2
  have hfbot : f p.1 ≠ ⊥ := hf.2.2 p.1 trivial
  lift f p.1 to ℝ using ⟨hftop, hfbot⟩ with α hα
  -- every term of the defining supremum is at most L·∑|x-p.1| + α
  have hbound : fenchelConjugate n (restrictCube L (fenchelConjugate n f)) x
      ≤ ((L * ∑ i, |(x - p.1) i| + α : ℝ) : EReal) := by
    rw [fenchelConjugate_eq_iSup]
    refine iSup_le fun u => ?_
    by_cases hu : u ∈ cube (n := n) L
    · rw [restrictCube_of_mem hu]
      have hFY : ((p.1 ⬝ᵥ u : ℝ) : EReal) - ((α : ℝ) : EReal)
          ≤ fenchelConjugate n f u := by
        have h := coe_sub_le_fenchelConjugate f p.1 u
        rwa [← hα] at h
      by_cases hcu : fenchelConjugate n f u = ⊤
      · rw [hcu, EReal.sub_top]
        exact bot_le
      · have hcbot := fenchelConjugate_ne_bot hf u
        lift fenchelConjugate n f u to ℝ using ⟨hcu, hcbot⟩ with β hβ
        have hFY' : p.1 ⬝ᵥ u - α ≤ β := by
          rw [← EReal.coe_sub] at hFY
          exact_mod_cast hFY
        rw [← EReal.coe_sub]
        refine EReal.coe_le_coe_iff.mpr ?_
        have hdot : u ⬝ᵥ (x - p.1) ≤ L * ∑ i, |(x - p.1) i| :=
          dotProduct_le_of_mem_cube hu (x - p.1)
        have hswap : u ⬝ᵥ x - (p.1 ⬝ᵥ u - α) = u ⬝ᵥ (x - p.1) + α := by
          rw [dotProduct_sub, dotProduct_comm p.1 u]
          ring
        linarith [hFY', hdot, hswap]
    · rw [restrictCube_of_not_mem hu (fenchelConjugate_ne_bot hf u), EReal.sub_top]
      exact bot_le
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hbound

/-- The regularized function is nowhere `⊥`, given a dual domain point in the
cube. -/
theorem regularized_ne_bot {f : (Fin n → ℝ) → EReal} {L : ℝ}
    (hf : ProperConvexFunctionOn Set.univ f)
    {u₀ : Fin n → ℝ} (hu₀ : u₀ ∈ cube (n := n) L)
    (hu₀top : fenchelConjugate n f u₀ ≠ ⊤) (x : Fin n → ℝ) :
    fenchelConjugate n (restrictCube L (fenchelConjugate n f)) x ≠ ⊥ := by
  have hle : ((u₀ ⬝ᵥ x : ℝ) : EReal) - restrictCube L (fenchelConjugate n f) u₀
      ≤ fenchelConjugate n (restrictCube L (fenchelConjugate n f)) x :=
    coe_sub_le_fenchelConjugate _ u₀ x
  rw [restrictCube_of_mem hu₀] at hle
  intro hzero
  rw [hzero, le_bot_iff] at hle
  lift fenchelConjugate n f u₀ to ℝ using ⟨hu₀top, fenchelConjugate_ne_bot hf u₀⟩
    with β hβ
  rw [← EReal.coe_sub] at hle
  exact EReal.coe_ne_bot _ hle

/-! ## The P-order passes to restricted conjugates -/

theorem pOrderE_restrictCube {φ ψ : (Fin n → ℝ) → EReal} (L : ℝ)
    (hφbot : ∀ u, φ u ≠ ⊥) (hψbot : ∀ u, ψ u ≠ ⊥)
    (hP : POrderE φ ψ) : POrderE (restrictCube L φ) (restrictCube L ψ) := by
  intro p p'
  by_cases hp : p ∈ cube (n := n) L
  · by_cases hp' : p' ∈ cube (n := n) L
    · have hmeet : p ⊓ p' ∈ cube (n := n) L :=
        ⟨le_inf hp.1 hp'.1, le_trans inf_le_left hp.2⟩
      have hjoin : p ⊔ p' ∈ cube (n := n) L :=
        ⟨le_trans hp.1 le_sup_left, sup_le hp.2 hp'.2⟩
      rw [restrictCube_of_mem hp, restrictCube_of_mem hp',
        restrictCube_of_mem hmeet, restrictCube_of_mem hjoin]
      exact hP p p'
    · rw [restrictCube_of_not_mem hp' (hψbot p'),
        EReal.add_top_of_ne_bot (by
          by_cases h : p ∈ cube (n := n) L
          · rw [restrictCube_of_mem h]; exact hφbot p
          · rw [restrictCube_of_not_mem h (hφbot p)]; simp)]
      exact le_top
  · rw [restrictCube_of_not_mem hp (hφbot p), EReal.top_add_of_ne_bot (by
      by_cases h : p' ∈ cube (n := n) L
      · rw [restrictCube_of_mem h]; exact hψbot p'
      · rw [restrictCube_of_not_mem h (hψbot p')]; simp)]
    exact le_top

/-! ## Bridge: a finite EReal convex function is a real `ConvexOn` -/

theorem convexOn_toReal_of_convexFunction {φ : (Fin n → ℝ) → EReal}
    {F : (Fin n → ℝ) → ℝ} (hφ : ConvexFunction φ)
    (hcoe : ∀ x, φ x = ((F x : ℝ) : EReal)) : ConvexOn ℝ Set.univ F := by
  refine convexOn_of_convex_epigraph ?_
  have hset : {p : (Fin n → ℝ) × ℝ | p.1 ∈ Set.univ ∧ F p.1 ≤ p.2}
      = epigraph Set.univ φ := by
    ext p
    constructor
    · rintro ⟨-, h⟩
      refine ⟨trivial, ?_⟩
      rw [hcoe]
      exact_mod_cast h
    · rintro ⟨-, h⟩
      rw [hcoe] at h
      exact ⟨trivial, by exact_mod_cast h⟩
  rw [hset]
  exact hφ

/-! ## The regularized function and the main theorem -/

/-- The Pasch–Hausdorff regularization, seen from the dual side. -/
noncomputable def regularize (L : ℝ) (f : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fenchelConjugate n (restrictCube L (fenchelConjugate n f))

/-- **P ⟹ Q in full generality (GHS Theorem 4, deep direction).** For closed
proper convex `f, g` on `ℝⁿ`, if `g* ≤_P f*` then `f ≤_Q g`. -/
theorem qOrderE_of_pOrderE_fenchelConjugate {f g : (Fin n → ℝ) → EReal}
    (hf_lsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f)
    (hg_lsc : LowerSemicontinuous g) (hg : ProperConvexFunctionOn Set.univ g)
    (hP : POrderE (fenchelConjugate n g) (fenchelConjugate n f)) :
    QOrderE f g := by
  intro q₁ q₂ δ₁ hδ₁
  have hfbot : ∀ x, f x ≠ ⊥ := fun x => hf.2.2 x trivial
  have hgbot : ∀ x, g x ≠ ⊥ := fun x => hg.2.2 x trivial
  -- trivial cases: an infinite right-hand side
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
  -- dual domain points and the threshold N₀
  obtain ⟨u₀, hu₀⟩ := exists_fenchelConjugate_ne_top hf_lsc hf
  obtain ⟨v₀, hv₀⟩ := exists_fenchelConjugate_ne_top hg_lsc hg
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (∑ i, (|u₀ i| + |v₀ i|))
  have habs : ∀ w : Fin n → ℝ, (∀ i, |w i| ≤ ∑ j, (|u₀ j| + |v₀ j|)) →
      ∀ L : ℕ, N₀ ≤ L → w ∈ cube (n := n) (L : ℝ) := by
    intro w hw L hL
    rw [mem_cube_iff]
    intro i
    calc |w i| ≤ ∑ j, (|u₀ j| + |v₀ j|) := hw i
      _ ≤ (N₀ : ℝ) := hN₀
      _ ≤ (L : ℝ) := by exact_mod_cast hL
  have hu₀mem : ∀ L : ℕ, N₀ ≤ L → u₀ ∈ cube (n := n) (L : ℝ) := by
    refine habs u₀ (fun i => ?_)
    calc |u₀ i| ≤ |u₀ i| + |v₀ i| := le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ ∑ j, (|u₀ j| + |v₀ j|) :=
          Finset.single_le_sum (f := fun j => |u₀ j| + |v₀ j|)
            (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
  have hv₀mem : ∀ L : ℕ, N₀ ≤ L → v₀ ∈ cube (n := n) (L : ℝ) := by
    refine habs v₀ (fun i => ?_)
    calc |v₀ i| ≤ |u₀ i| + |v₀ i| := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ ∑ j, (|u₀ j| + |v₀ j|) :=
          Finset.single_le_sum (f := fun j => |u₀ j| + |v₀ j|)
            (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
  -- standing facts about the conjugates
  have hcf_lsc : LowerSemicontinuous (fenchelConjugate n f) :=
    (fenchelConjugate_closedConvex (n := n) (f := f)).1
  have hcg_lsc : LowerSemicontinuous (fenchelConjugate n g) :=
    (fenchelConjugate_closedConvex (n := n) (f := g)).1
  have hcf_proper : ProperConvexFunctionOn Set.univ (fenchelConjugate n f) :=
    fenchelConjugate_proper hf_lsc hf
  have hcg_proper : ProperConvexFunctionOn Set.univ (fenchelConjugate n g) :=
    fenchelConjugate_proper hg_lsc hg
  have hcf_bot := fenchelConjugate_ne_bot hf
  have hcg_bot := fenchelConjugate_ne_bot hg
  -- monotonicity of the regularization
  have hreg_le_f : ∀ (L : ℝ) (x : Fin n → ℝ), regularize L f x ≤ f x := by
    intro L x
    calc regularize L f x
        ≤ fenchelConjugate n (fenchelConjugate n f) x :=
          fenchelConjugate_antitone n
            (le_restrictCube L (fenchelConjugate n f)) x
      _ = f x := congrFun (fenchelConjugate_fenchelConjugate_eq hf_lsc hf) x
  have hreg_le_g : ∀ (L : ℝ) (x : Fin n → ℝ), regularize L g x ≤ g x := by
    intro L x
    calc regularize L g x
        ≤ fenchelConjugate n (fenchelConjugate n g) x :=
          fenchelConjugate_antitone n
            (le_restrictCube L (fenchelConjugate n g)) x
      _ = g x := congrFun (fenchelConjugate_fenchelConjugate_eq hg_lsc hg) x
  have hreg_mono_f : ∀ {L L' : ℝ}, L ≤ L' → ∀ x, regularize L f x ≤ regularize L' f x :=
    fun {L L'} h x =>
      fenchelConjugate_antitone n (restrictCube_antitone h (fenchelConjugate n f)) x
  have hreg_mono_g : ∀ {L L' : ℝ}, L ≤ L' → ∀ x, regularize L g x ≤ regularize L' g x :=
    fun {L L'} h x =>
      fenchelConjugate_antitone n (restrictCube_antitone h (fenchelConjugate n g)) x
  -- the exchange witnesses for the regularized pair
  have hex : ∀ L : ℕ, N₀ ≤ L → ∃ δ₂ ∈ Icc 0 ((q₁ - q₂)⁻),
      regularize (L : ℝ) f (q₁ - (δ₁ - δ₂)) + regularize (L : ℝ) g (q₂ + (δ₁ - δ₂))
        ≤ regularize (L : ℝ) f q₁ + regularize (L : ℝ) g q₂ := by
    intro L hL
    have hφf_lsc := lowerSemicontinuous_restrictCube (L : ℝ) hcf_lsc hcf_bot
    have hφg_lsc := lowerSemicontinuous_restrictCube (L : ℝ) hcg_lsc hcg_bot
    have hφf_proper := properConvexOn_restrictCube hcf_proper u₀ (hu₀mem L hL) hu₀
    have hφg_proper := properConvexOn_restrictCube hcg_proper v₀ (hv₀mem L hL) hv₀
    have hFtop : ∀ x, regularize (L : ℝ) f x ≠ ⊤ := regularized_ne_top hf
    have hFbot : ∀ x, regularize (L : ℝ) f x ≠ ⊥ :=
      regularized_ne_bot hf (hu₀mem L hL) hu₀
    have hGtop : ∀ x, regularize (L : ℝ) g x ≠ ⊤ := regularized_ne_top hg
    have hGbot : ∀ x, regularize (L : ℝ) g x ≠ ⊥ :=
      regularized_ne_bot hg (hv₀mem L hL) hv₀
    set Fr : (Fin n → ℝ) → ℝ := fun x => (regularize (L : ℝ) f x).toReal with hFr
    set Gr : (Fin n → ℝ) → ℝ := fun x => (regularize (L : ℝ) g x).toReal with hGr
    have hFcoe : ∀ x, regularize (L : ℝ) f x = ((Fr x : ℝ) : EReal) := fun x =>
      (EReal.coe_toReal (hFtop x) (hFbot x)).symm
    have hGcoe : ∀ x, regularize (L : ℝ) g x = ((Gr x : ℝ) : EReal) := fun x =>
      (EReal.coe_toReal (hGtop x) (hGbot x)).symm
    have hFconv : ConvexOn ℝ Set.univ Fr :=
      convexOn_toReal_of_convexFunction
        (fenchelConjugate_closedConvex (n := n)
          (f := restrictCube (L : ℝ) (fenchelConjugate n f))).2 hFcoe
    have hGconv : ConvexOn ℝ Set.univ Gr :=
      convexOn_toReal_of_convexFunction
        (fenchelConjugate_closedConvex (n := n)
          (f := restrictCube (L : ℝ) (fenchelConjugate n g))).2 hGcoe
    -- the P-order at the restricted level, transported to the real pair
    have hφP : POrderE (restrictCube (L : ℝ) (fenchelConjugate n g))
        (restrictCube (L : ℝ) (fenchelConjugate n f)) :=
      pOrderE_restrictCube (L : ℝ) hcg_bot hcf_bot hP
    have hconjF : fenchelConjugate n (fun x => ((Fr x : ℝ) : EReal))
        = restrictCube (L : ℝ) (fenchelConjugate n f) := by
      have hfun : (fun x => ((Fr x : ℝ) : EReal)) = regularize (L : ℝ) f :=
        funext fun x => (hFcoe x).symm
      rw [hfun]
      show fenchelConjugate n
        (fenchelConjugate n (restrictCube (L : ℝ) (fenchelConjugate n f))) = _
      exact fenchelConjugate_fenchelConjugate_eq hφf_lsc hφf_proper
    have hconjG : fenchelConjugate n (fun x => ((Gr x : ℝ) : EReal))
        = restrictCube (L : ℝ) (fenchelConjugate n g) := by
      have hfun : (fun x => ((Gr x : ℝ) : EReal)) = regularize (L : ℝ) g :=
        funext fun x => (hGcoe x).symm
      rw [hfun]
      show fenchelConjugate n
        (fenchelConjugate n (restrictCube (L : ℝ) (fenchelConjugate n g))) = _
      exact fenchelConjugate_fenchelConjugate_eq hφg_lsc hφg_proper
    have hPr : POrderE (fenchelConjugate n (fun x => ((Gr x : ℝ) : EReal)))
        (fenchelConjugate n (fun x => ((Fr x : ℝ) : EReal))) := by
      rw [hconjF, hconjG]
      exact hφP
    obtain ⟨δ₂, hδ₂, hkey⟩ :=
      qOrderE_coe_of_pOrder_fenchelConjugate hFconv hGconv hPr q₁ q₂ δ₁ hδ₁
    refine ⟨δ₂, hδ₂, ?_⟩
    rw [hFcoe, hGcoe, hFcoe, hGcoe]
    exact hkey
  -- the witness sequence and its convergent subsequence
  classical
  set δs : ℕ → (Fin n → ℝ) :=
    fun L => if h : N₀ ≤ L then (hex L h).choose else 0 with hδs
  have hδs_mem : ∀ L, δs L ∈ Icc (0 : Fin n → ℝ) ((q₁ - q₂)⁻) := by
    intro L
    by_cases h : N₀ ≤ L
    · simp only [hδs, dif_pos h]
      exact (hex L h).choose_spec.1
    · simp only [hδs, dif_neg h]
      exact ⟨le_refl 0, negPart_nonneg _⟩
  have hδs_key : ∀ L : ℕ, N₀ ≤ L →
      regularize (L : ℝ) f (q₁ - (δ₁ - δs L)) + regularize (L : ℝ) g (q₂ + (δ₁ - δs L))
        ≤ regularize (L : ℝ) f q₁ + regularize (L : ℝ) g q₂ := by
    intro L h
    simp only [hδs, dif_pos h]
    exact (hex L h).choose_spec.2
  obtain ⟨δstar, hδstar_mem, ψ, hψmono, hψtend⟩ :=
    (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := (q₁ - q₂)⁻)).tendsto_subseq hδs_mem
  refine ⟨δstar, hδstar_mem, ?_⟩
  -- reduce to real strict lower bounds via density
  refine EReal.add_le_of_forall_lt fun y hy z hz => ?_
  -- y < f(a*) is witnessed at some finite regularization level
  have hyM : ∃ M : ℕ, N₀ ≤ M ∧ y < regularize (M : ℝ) f (q₁ - (δ₁ - δstar)) := by
    have hbi : f (q₁ - (δ₁ - δstar))
        = fenchelConjugate n (fenchelConjugate n f) (q₁ - (δ₁ - δstar)) :=
      (congrFun (fenchelConjugate_fenchelConjugate_eq hf_lsc hf) _).symm
    rw [hbi, fenchelConjugate_eq_iSup] at hy
    obtain ⟨u, hu⟩ := lt_iSup_iff.mp hy
    obtain ⟨M₁, hM₁⟩ := exists_nat_ge (∑ i, |u i|)
    refine ⟨max M₁ N₀, le_max_right _ _, ?_⟩
    have humem : u ∈ cube (n := n) ((max M₁ N₀ : ℕ) : ℝ) := by
      rw [mem_cube_iff]
      intro i
      calc |u i| ≤ ∑ j, |u j| :=
            Finset.single_le_sum (f := fun j => |u j|)
              (fun j _ => abs_nonneg _) (Finset.mem_univ i)
        _ ≤ (M₁ : ℝ) := hM₁
        _ ≤ ((max M₁ N₀ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hterm := coe_sub_le_fenchelConjugate
      (restrictCube ((max M₁ N₀ : ℕ) : ℝ) (fenchelConjugate n f)) u
      (q₁ - (δ₁ - δstar))
    rw [restrictCube_of_mem humem] at hterm
    exact lt_of_lt_of_le hu hterm
  have hzM : ∃ M : ℕ, N₀ ≤ M ∧ z < regularize (M : ℝ) g (q₂ + (δ₁ - δstar)) := by
    have hbi : g (q₂ + (δ₁ - δstar))
        = fenchelConjugate n (fenchelConjugate n g) (q₂ + (δ₁ - δstar)) :=
      (congrFun (fenchelConjugate_fenchelConjugate_eq hg_lsc hg) _).symm
    rw [hbi, fenchelConjugate_eq_iSup] at hz
    obtain ⟨u, hu⟩ := lt_iSup_iff.mp hz
    obtain ⟨M₁, hM₁⟩ := exists_nat_ge (∑ i, |u i|)
    refine ⟨max M₁ N₀, le_max_right _ _, ?_⟩
    have humem : u ∈ cube (n := n) ((max M₁ N₀ : ℕ) : ℝ) := by
      rw [mem_cube_iff]
      intro i
      calc |u i| ≤ ∑ j, |u j| :=
            Finset.single_le_sum (f := fun j => |u j|)
              (fun j _ => abs_nonneg _) (Finset.mem_univ i)
        _ ≤ (M₁ : ℝ) := hM₁
        _ ≤ ((max M₁ N₀ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hterm := coe_sub_le_fenchelConjugate
      (restrictCube ((max M₁ N₀ : ℕ) : ℝ) (fenchelConjugate n g)) u
      (q₂ + (δ₁ - δstar))
    rw [restrictCube_of_mem humem] at hterm
    exact lt_of_lt_of_le hu hterm
  obtain ⟨M₁, hM₁N, hM₁⟩ := hyM
  obtain ⟨M₂, hM₂N, hM₂⟩ := hzM
  -- superlevel sets of the (l.s.c.) regularized functions are open
  have hopen1 : IsOpen {x : Fin n → ℝ | y < regularize (M₁ : ℝ) f x} :=
    lowerSemicontinuous_iff_isOpen_preimage.mp
      (fenchelConjugate_closedConvex (n := n)
        (f := restrictCube ((M₁ : ℕ) : ℝ) (fenchelConjugate n f))).1 y
  have hopen2 : IsOpen {x : Fin n → ℝ | z < regularize (M₂ : ℝ) g x} :=
    lowerSemicontinuous_iff_isOpen_preimage.mp
      (fenchelConjugate_closedConvex (n := n)
        (f := restrictCube ((M₂ : ℕ) : ℝ) (fenchelConjugate n g))).1 z
  -- convergence of the moved points along the subsequence
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
  have hev1 : ∀ᶠ k in Filter.atTop, y < regularize (M₁ : ℝ) f (q₁ - (δ₁ - δs (ψ k))) :=
    htend_a.eventually (hopen1.mem_nhds hM₁)
  have hev2 : ∀ᶠ k in Filter.atTop, z < regularize (M₂ : ℝ) g (q₂ + (δ₁ - δs (ψ k))) :=
    htend_b.eventually (hopen2.mem_nhds hM₂)
  have hev3 : ∀ᶠ k in Filter.atTop, max M₁ M₂ ≤ ψ k :=
    (Filter.eventually_ge_atTop (max M₁ M₂)).mono fun k hk =>
      le_trans hk (hψmono.le_apply)
  obtain ⟨k, hk1, hk2, hk3⟩ := (hev1.and (hev2.and hev3)).exists
  -- assemble the bound at level ψ k
  have hNψ : N₀ ≤ ψ k := le_trans hM₁N (le_trans (le_max_left _ _) hk3)
  have hM₁ψ : (M₁ : ℝ) ≤ ((ψ k : ℕ) : ℝ) := by
    exact_mod_cast le_trans (le_max_left M₁ M₂) hk3
  have hM₂ψ : (M₂ : ℝ) ≤ ((ψ k : ℕ) : ℝ) := by
    exact_mod_cast le_trans (le_max_right M₁ M₂) hk3
  have hy' : y ≤ regularize ((ψ k : ℕ) : ℝ) f (q₁ - (δ₁ - δs (ψ k))) :=
    le_trans hk1.le (hreg_mono_f hM₁ψ _)
  have hz' : z ≤ regularize ((ψ k : ℕ) : ℝ) g (q₂ + (δ₁ - δs (ψ k))) :=
    le_trans hk2.le (hreg_mono_g hM₂ψ _)
  have hle1 : regularize ((ψ k : ℕ) : ℝ) f q₁ ≤ ((α : ℝ) : EReal) := by
    rw [hα]
    exact hreg_le_f _ q₁
  have hle2 : regularize ((ψ k : ℕ) : ℝ) g q₂ ≤ ((β : ℝ) : EReal) := by
    rw [hβ]
    exact hreg_le_g _ q₂
  calc y + z
      ≤ regularize ((ψ k : ℕ) : ℝ) f (q₁ - (δ₁ - δs (ψ k)))
        + regularize ((ψ k : ℕ) : ℝ) g (q₂ + (δ₁ - δs (ψ k))) := add_le_add hy' hz'
    _ ≤ regularize ((ψ k : ℕ) : ℝ) f q₁ + regularize ((ψ k : ℕ) : ℝ) g q₂ :=
        hδs_key (ψ k) hNψ
    _ ≤ ((α : ℝ) : EReal) + ((β : ℝ) : EReal) := add_le_add hle1 hle2

end GHS
