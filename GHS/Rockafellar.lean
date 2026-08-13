import Mathlib

/-!
# Finite-dimensional convex conjugacy

A small, self-contained convex-analysis layer for the GHS development.  The
definitions use `EReal` so that closed convex functions may take the value
`⊤`; unlike the former experimental dependency, this file depends only on
Mathlib.
-/

open Set

namespace GHS

/-- The (real-height) epigraph of an extended-real-valued function. -/
def epigraph {n : ℕ} (S : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → EReal) :
    Set ((Fin n → ℝ) × ℝ) :=
  {p | p.1 ∈ S ∧ f p.1 ≤ (p.2 : EReal)}

/-- Convexity of an extended-real-valued function on a set, expressed by its epigraph. -/
def ConvexFunctionOn {n : ℕ} (S : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → EReal) : Prop :=
  Convex ℝ (epigraph S f)

/-- Convexity on the whole finite-dimensional space. -/
def ConvexFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ConvexFunctionOn Set.univ f

/-- A convex function with nonempty epigraph which never takes `⊥`. -/
def ProperConvexFunctionOn {n : ℕ} (S : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal) : Prop :=
  ConvexFunctionOn S f ∧ (epigraph S f).Nonempty ∧ ∀ x ∈ S, f x ≠ ⊥

/-- The effective domain of an extended-real-valued function. -/
def effectiveDomain {n : ℕ} (S : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | x ∈ S ∧ f x < ⊤}

theorem effectiveDomain_eq {n : ℕ} (S : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal) :
    effectiveDomain S f = S ∩ {x | f x < ⊤} := rfl

/-- Fenchel conjugation for the standard Euclidean pairing. -/
noncomputable def fenchelConjugate (n : ℕ) (f : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun xStar => sSup (Set.range fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x)

/-- Infimal convolution of a finite family, expressed through all additive
decompositions of the argument. -/
noncomputable def infimalConvolutionFamily {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : EReal :=
  sInf {r | ∃ x' : Fin m → (Fin n → ℝ),
    (∑ i, x' i) = x ∧ r = ∑ i, f i (x' i)}

theorem fenchelConjugate_eq_iSup (n : ℕ) (f : (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) :
    fenchelConjugate n f xStar = ⨆ x, ((x ⬝ᵥ xStar : ℝ) : EReal) - f x := by
  simp [fenchelConjugate, sSup_range]

/-- Fenchel conjugation reverses pointwise order. -/
theorem fenchelConjugate_antitone (n : ℕ) {f g : (Fin n → ℝ) → EReal}
    (h : f ≤ g) : fenchelConjugate n g ≤ fenchelConjugate n f := by
  intro u
  rw [fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup]
  exact iSup_mono fun x => EReal.sub_le_sub le_rfl (h x)

/-- Addition distributes over two unrestricted suprema in `EReal`. -/
theorem section16_iSup_add_iSup_eq_iSup_prod {α β : Type*}
    (u : α → EReal) (v : β → EReal) :
    (⨆ a, u a) + (⨆ b, v b) = ⨆ p : α × β, u p.1 + v p.2 := by
  apply le_antisymm
  · refine EReal.add_le_of_forall_lt fun x hx y hy => ?_
    obtain ⟨a, ha⟩ := (lt_iSup_iff).mp hx
    obtain ⟨b, hb⟩ := (lt_iSup_iff).mp hy
    exact (add_le_add ha.le hb.le).trans
      (le_iSup (fun p : α × β => u p.1 + v p.2) (a, b))
  · refine iSup_le fun p => add_le_add (le_iSup u p.1) (le_iSup v p.2)

/-! ## Supporting subgradients for finite convex functions -/

/-- A vector subgradient for a real-valued function on a Euclidean coordinate space. -/
def Subgradient {k : ℕ} (f : (Fin k → ℝ) → ℝ) (x q : Fin k → ℝ) : Prop :=
  ∀ y, f x + q ⬝ᵥ (y - x) ≤ f y

/-- A continuous-linear subgradient on a normed real vector space. -/
def LinearSubgradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (q : StrongDual ℝ E) : Prop :=
  ∀ y, f x + q (y - x) ≤ f y

/-- A continuous convex real-valued function has a continuous-linear subgradient.
This form is convenient for product spaces. -/
theorem exists_linearSubgradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (hfc : Continuous f) (x : E) :
    ∃ q : StrongDual ℝ E, LinearSubgradient f x q := by
  let T : Set (E × ℝ) := {p | f p.1 < p.2}
  have hTconv : Convex ℝ T := by simpa [T] using hf.convex_strict_epigraph
  have hTopen : IsOpen T := by
    simpa [T] using isOpen_lt (hfc.comp continuous_fst) continuous_snd
  have hxnot : (x, f x) ∉ T := by simp [T]
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_open hTconv hTopen hxnot
  let c : ℝ := l (0, 1)
  let a : StrongDual ℝ E := l.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hdecomp (z : E) (r : ℝ) : l (z, r) = a z + r * c := by
    have hp : (z, r) = (z, 0) + (0, r) := by ext <;> simp
    have hlr : l (0, r) = r * l (0, 1) := by
      have heq : (0, r) = r • ((0 : E), (1 : ℝ)) := by ext <;> simp
      rw [heq, map_smul, smul_eq_mul]
    rw [hp, map_add, hlr]
    change l (z, 0) + r * l (0, 1) = l (z, 0) + r * l (0, 1)
    rfl
  have hc : 0 < c := by
    have hone := hl (x, f x + 1) (by simp [T])
    rw [hdecomp, hdecomp] at hone
    linarith
  have hsupport (y : E) : l (x, f x) ≤ l (y, f y) := by
    refine le_of_forall_pos_le_add fun e he => ?_
    have hec : 0 < e / c := div_pos he hc
    have hsep := hl (y, f y + e / c) (by simp [T, hec])
    rw [hdecomp, hdecomp] at hsep
    have heq : a y + (f y + e / c) * c = (a y + f y * c) + e := by
      field_simp [ne_of_gt hc]
      ring
    rw [heq] at hsep
    simpa [hdecomp] using hsep.le
  let q : StrongDual ℝ E := (-c⁻¹) • a
  refine ⟨q, fun y => ?_⟩
  have hs := hsupport y
  rw [hdecomp, hdecomp] at hs
  have hnum : a x - a y ≤ (f y - f x) * c := by
    calc
      a x - a y ≤ f y * c - f x * c := by linarith [hs]
      _ = (f y - f x) * c := by ring
  have hq : q (y - x) = (a x - a y) / c := by
    simp [q, map_sub]
    field_simp [ne_of_gt hc]
    ring
  rw [hq]
  calc
    f x + (a x - a y) / c ≤ f x + (f y - f x) := by
      simpa [add_comm] using add_le_add_left ((div_le_iff₀ hc).2 hnum) (f x)
    _ = f y := by ring

/-- Every finite convex function on a whole finite-dimensional space has a subgradient.

The proof separates the boundary point `(x,f x)` from the open strict epigraph.
The coefficient of the height coordinate is positive, so the separating functional
can be normalized to a vector subgradient. -/
theorem exists_subgradient {k : ℕ} (f : (Fin k → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (x : Fin k → ℝ) :
    ∃ q, Subgradient f x q := by
  classical
  let T : Set ((Fin k → ℝ) × ℝ) := {p | f p.1 < p.2}
  have hTconv : Convex ℝ T := by
    simpa [T] using hf.convex_strict_epigraph
  have hfcont : Continuous f := hf.locallyLipschitz.continuous
  have hTopen : IsOpen T := by
    simpa [T] using isOpen_lt (hfcont.comp continuous_fst) continuous_snd
  have hxnot : (x, f x) ∉ T := by simp [T]
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_open hTconv hTopen hxnot
  let c : ℝ := l (0, 1)
  let g : (Fin k → ℝ) →ₗ[ℝ] ℝ := l.toLinearMap.comp (LinearMap.inl ℝ _ ℝ)
  let a : Fin k → ℝ := (dotProductEquiv ℝ (Fin k)).symm g
  have ha (z : Fin k → ℝ) : a ⬝ᵥ z = g z := by
    change (dotProductEquiv ℝ (Fin k) a) z = g z
    rw [show dotProductEquiv ℝ (Fin k) a = g by
      exact LinearEquiv.apply_symm_apply (dotProductEquiv ℝ (Fin k)) g]
  have hdecomp (z : Fin k → ℝ) (r : ℝ) : l (z, r) = z ⬝ᵥ a + r * c := by
    have hp : (z, r) = (z, 0) + (0, r) := by ext <;> simp
    have hlr : l (0, r) = r * l (0, 1) := by
      have heq : (0, r) = r • ((0 : Fin k → ℝ), (1 : ℝ)) := by ext <;> simp
      rw [heq, map_smul, smul_eq_mul]
    rw [hp, map_add, hlr]
    have hgz : l (z, 0) = g z := rfl
    rw [hgz, ← ha, dotProduct_comm]
  have hc : 0 < c := by
    have hone := hl (x, f x + 1) (by simp [T])
    rw [hdecomp, hdecomp] at hone
    linarith
  have hsupport (y : Fin k → ℝ) : l (x, f x) ≤ l (y, f y) := by
    refine le_of_forall_pos_le_add fun e he => ?_
    have hec : 0 < e / c := div_pos he hc
    have hsep := hl (y, f y + e / c) (by simp [T, hec])
    rw [hdecomp, hdecomp] at hsep
    have heq : y ⬝ᵥ a + (f y + e / c) * c =
        (y ⬝ᵥ a + f y * c) + e := by field_simp [ne_of_gt hc]; ring
    rw [heq] at hsep
    simpa [hdecomp] using hsep.le
  let q : Fin k → ℝ := fun i => -a i / c
  refine ⟨q, fun y => ?_⟩
  have hs := hsupport y
  rw [hdecomp, hdecomp] at hs
  have hdot : q ⬝ᵥ (y - x) = (x ⬝ᵥ a - y ⬝ᵥ a) / c := by
    simp only [dotProduct, q, Pi.sub_apply]
    rw [eq_div_iff (ne_of_gt hc), Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt hc]
    ring
  rw [hdot]
  have hnum : x ⬝ᵥ a - y ⬝ᵥ a ≤ (f y - f x) * c := by
    calc
      x ⬝ᵥ a - y ⬝ᵥ a ≤ f y * c - f x * c := by linarith [hs]
      _ = (f y - f x) * c := by ring
  calc
    f x + (x ⬝ᵥ a - y ⬝ᵥ a) / c
        ≤ f x + (f y - f x) := by
          simpa [add_comm] using add_le_add_left ((div_le_iff₀ hc).2 hnum) (f x)
    _ = f y := by ring

/-! ## Closedness and convexity of conjugates -/

/-- A Fenchel conjugate is lower semicontinuous and convex. -/
theorem fenchelConjugate_closedConvex (n : ℕ) (f : (Fin n → ℝ) → EReal) :
    LowerSemicontinuous (fenchelConjugate n f) ∧
      ConvexFunction (fenchelConjugate n f) := by
  classical
  let A : (Fin n → ℝ) → (Fin n → ℝ) → EReal :=
    fun x u => ((x ⬝ᵥ u : ℝ) : EReal) - f x
  have hA_lsc (x : Fin n → ℝ) : LowerSemicontinuous (A x) := by
    by_cases htop : f x = ⊤
    · have he : A x = fun _ : Fin n → ℝ => (⊥ : EReal) := by funext u; simp [A, htop]
      rw [he]
      exact continuous_const.lowerSemicontinuous
    by_cases hbot : f x = ⊥
    · have he : A x = fun _ : Fin n → ℝ => (⊤ : EReal) := by funext u; simp [A, hbot]
      rw [he]
      exact continuous_const.lowerSemicontinuous
    lift f x to ℝ using ⟨htop, hbot⟩ with r hr
    have hreal : Continuous (fun u : Fin n → ℝ => x ⬝ᵥ u - r) := by fun_prop
    have he : A x = fun u => ((x ⬝ᵥ u - r : ℝ) : EReal) := by
      funext u
      change ((x ⬝ᵥ u : ℝ) : EReal) - f x = _
      rw [← hr, ← EReal.coe_sub]
    rw [he]
    exact (continuous_coe_real_ereal.comp hreal).lowerSemicontinuous
  have hlsc : LowerSemicontinuous (fenchelConjugate n f) := by
    have hi := lowerSemicontinuous_iSup hA_lsc
    simpa [A, fenchelConjugate_eq_iSup] using hi
  have hA_conv (x : Fin n → ℝ) : ConvexFunction (A x) := by
    by_cases htop : f x = ⊤
    ·
        have he : epigraph Set.univ (A x) = Set.univ := by
          ext p
          constructor
          · intro; trivial
          · intro; exact ⟨trivial, by simp [A, htop]⟩
        simpa [ConvexFunction, ConvexFunctionOn, he] using
          (convex_univ : Convex ℝ (Set.univ : Set ((Fin n → ℝ) × ℝ)))
    by_cases hbot : f x = ⊥
    ·
        have he : epigraph Set.univ (A x) = (∅ : Set ((Fin n → ℝ) × ℝ)) := by
          ext p
          constructor
          · rintro ⟨-, hp⟩
            simp [A, hbot] at hp
          · simp
        simpa [ConvexFunction, ConvexFunctionOn, he] using
          (convex_empty : Convex ℝ (∅ : Set ((Fin n → ℝ) × ℝ)))
    ·
        lift f x to ℝ using ⟨htop, hbot⟩ with r hr
        let a : (Fin n → ℝ) → ℝ := fun u => x ⬝ᵥ u - r
        have ha : ConvexOn ℝ Set.univ a := by
          refine ⟨convex_univ, fun u _ v _ s t hs ht hst => ?_⟩
          dsimp [a]
          rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
          simp only [smul_eq_mul]
          apply le_of_eq
          linear_combination r * hst
        have he : epigraph Set.univ (A x) =
            {p : (Fin n → ℝ) × ℝ | p.1 ∈ Set.univ ∧ a p.1 ≤ p.2} := by
          ext p
          simp only [epigraph, mem_setOf_eq, mem_univ, true_and, A, a]
          rw [← hr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        rw [ConvexFunction, ConvexFunctionOn, he]
        exact ha.convex_epigraph
  have hconv : ConvexFunction (fenchelConjugate n f) := by
    have he : epigraph Set.univ (fenchelConjugate n f) =
        ⋂ x, epigraph Set.univ (A x) := by
      ext p
      simp only [epigraph, mem_setOf_eq, mem_iInter, mem_univ, true_and]
      rw [fenchelConjugate_eq_iSup]
      exact iSup_le_iff
    rw [ConvexFunction, ConvexFunctionOn, he]
    exact convex_iInter fun x => hA_conv x
  exact ⟨hlsc, hconv⟩

theorem isClosed_epigraph {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : LowerSemicontinuous f) : IsClosed (epigraph Set.univ f) := by
  let e : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × EReal) := fun p => (p.1, (p.2 : EReal))
  have he : Continuous e := continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  have hpre : epigraph Set.univ f = e ⁻¹' {p : (Fin n → ℝ) × EReal | f p.1 ≤ p.2} := by
    ext p
    simp [epigraph, e]
  rw [hpre]
  exact (hf.isClosed_epigraph).preimage he

theorem continuousLinear_prod_decomp {n : ℕ}
    (l : StrongDual ℝ ((Fin n → ℝ) × ℝ)) :
    ∃ a : Fin n → ℝ, ∀ z r, l (z, r) = z ⬝ᵥ a + r * l (0, 1) := by
  let g : (Fin n → ℝ) →ₗ[ℝ] ℝ := l.toLinearMap.comp (LinearMap.inl ℝ _ ℝ)
  let a : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g
  have ha (z : Fin n → ℝ) : z ⬝ᵥ a = g z := by
    rw [dotProduct_comm]
    change (dotProductEquiv ℝ (Fin n) a) z = g z
    rw [show dotProductEquiv ℝ (Fin n) a = g from
      LinearEquiv.apply_symm_apply (dotProductEquiv ℝ (Fin n)) g]
  refine ⟨a, fun z r => ?_⟩
  have hp : (z, r) = (z, 0) + (0, r) := by ext <;> simp
  have hr : l (0, r) = r * l (0, 1) := by
    have heq : (0, r) = r • ((0 : Fin n → ℝ), (1 : ℝ)) := by ext <;> simp
    rw [heq, map_smul, smul_eq_mul]
  rw [hp, map_add, hr, ha]
  rfl

/-- A closed proper convex function has a finite affine minorant. -/
theorem exists_affineMinorant {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hlsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f) :
    ∃ u : Fin n → ℝ, ∃ β : ℝ, ∀ x, ((β + x ⬝ᵥ u : ℝ) : EReal) ≤ f x := by
  classical
  obtain ⟨p, hp⟩ := hf.2.1
  have hpbot : f p.1 ≠ ⊥ := hf.2.2 p.1 trivial
  have hptop : f p.1 ≠ ⊤ := by
    intro h
    have hp2 := hp.2
    rw [h] at hp2
    exact EReal.coe_ne_top p.2 (top_le_iff.mp hp2)
  lift f p.1 to ℝ using ⟨hptop, hpbot⟩ with r hr
  let z : (Fin n → ℝ) × ℝ := (p.1, r - 1)
  have hz : z ∉ epigraph Set.univ f := by
    intro h
    have h2 := h.2
    rw [← hr] at h2
    exact (not_le_of_gt (EReal.coe_lt_coe_iff.mpr (by linarith))) h2
  obtain ⟨l, q, hl, hlz⟩ := geometric_hahn_banach_closed_point hf.1
    (isClosed_epigraph hlsc) hz
  obtain ⟨a, ha⟩ := continuousLinear_prod_decomp l
  have hp' : (p.1, r) ∈ epigraph Set.univ f := by
    rw [epigraph]
    exact ⟨trivial, by rw [← hr]⟩
  have hsep := (hl _ hp').trans hlz
  dsimp [z] at hsep
  rw [ha p.1 r, ha p.1 (r - 1)] at hsep
  have hc : l (0, 1) < 0 := by linarith
  let u : Fin n → ℝ := fun i => -a i / l (0, 1)
  let β : ℝ := (r - 1) + p.1 ⬝ᵥ a / l (0, 1)
  refine ⟨u, β, fun x => ?_⟩
  by_cases hxtop : f x = ⊤
  · rw [hxtop]
    exact le_top
  have hxbot : f x ≠ ⊥ := hf.2.2 x trivial
  lift f x to ℝ using ⟨hxtop, hxbot⟩ with s hs
  have hxepi : (x, s) ∈ epigraph Set.univ f := ⟨trivial, by rw [← hs]⟩
  have hxy := (hl _ hxepi).trans hlz
  dsimp [z] at hxy
  rw [ha x s, ha p.1 (r - 1)] at hxy
  apply EReal.coe_le_coe_iff.mpr
  dsimp [u, β]
  have hdot : x ⬝ᵥ (fun i => -a i / l (0, 1)) = -(x ⬝ᵥ a) / l (0, 1) := by
    simp only [dotProduct]
    rw [eq_div_iff (ne_of_lt hc), Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by field_simp [ne_of_lt hc]
  rw [hdot]
  apply le_of_lt
  have hpdiv : (p.1 ⬝ᵥ a / l (0, 1)) * l (0, 1) = p.1 ⬝ᵥ a :=
    div_mul_cancel₀ _ (ne_of_lt hc)
  have hxdiv : (-(x ⬝ᵥ a) / l (0, 1)) * l (0, 1) = -(x ⬝ᵥ a) :=
    div_mul_cancel₀ _ (ne_of_lt hc)
  by_contra hn
  push_neg at hn
  have hmul := mul_le_mul_of_nonpos_right hn hc.le
  nlinarith

theorem fenchelConjugate_ne_bot_of_proper {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn Set.univ f) (u : Fin n → ℝ) :
    fenchelConjugate n f u ≠ ⊥ := by
  obtain ⟨p, hp⟩ := hf.2.1
  have hle : ((p.1 ⬝ᵥ u : ℝ) : EReal) - f p.1 ≤ fenchelConjugate n f u := by
    rw [fenchelConjugate_eq_iSup]
    exact le_iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ u : ℝ) : EReal) - f x) p.1
  have hpbot : f p.1 ≠ ⊥ := hf.2.2 p.1 trivial
  have hptop : f p.1 ≠ ⊤ := by
    intro h
    have h2 := hp.2
    rw [h] at h2
    exact EReal.coe_ne_top p.2 (top_le_iff.mp h2)
  lift f p.1 to ℝ using ⟨hptop, hpbot⟩ with r hr
  rw [← EReal.coe_sub] at hle
  intro h
  rw [h] at hle
  exact EReal.coe_ne_bot (p.1 ⬝ᵥ u - r) (le_bot_iff.mp hle)

theorem fenchelConjugate_le_of_affineMinorant {n : ℕ} {f : (Fin n → ℝ) → EReal}
    {u : Fin n → ℝ} {β : ℝ} (h : ∀ x, ((β + x ⬝ᵥ u : ℝ) : EReal) ≤ f x) :
    fenchelConjugate n f u ≤ ((-β : ℝ) : EReal) := by
  rw [fenchelConjugate_eq_iSup]
  refine iSup_le fun x => ?_
  by_cases htop : f x = ⊤
  · simp [htop]
  have hbot : f x ≠ ⊥ := by
    intro hb
    have hx := h x
    rw [hb] at hx
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hx)
  lift f x to ℝ using ⟨htop, hbot⟩ with r hr
  have hx : β + x ⬝ᵥ u ≤ r := by
    have := h x
    rw [← hr] at this
    exact EReal.coe_le_coe_iff.mp this
  rw [← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

theorem fenchelConjugate_proper {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hlsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f) :
    ProperConvexFunctionOn Set.univ (fenchelConjugate n f) := by
  obtain ⟨u, β, hminor⟩ := exists_affineMinorant hlsc hf
  have hutop : fenchelConjugate n f u ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top (-β)) (fenchelConjugate_le_of_affineMinorant hminor)
  have hubot := fenchelConjugate_ne_bot_of_proper hf u
  lift fenchelConjugate n f u to ℝ using ⟨hutop, hubot⟩ with r hr
  refine ⟨(fenchelConjugate_closedConvex n f).2,
    ⟨(u, r), trivial, by rw [← hr]⟩, fun x _ => fenchelConjugate_ne_bot_of_proper hf x⟩

/-- An affine minorant whose value at `x` reaches any prescribed real level below `f x`. -/
theorem exists_affineMinorant_gt {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hlsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f)
    {x : Fin n → ℝ} {R : ℝ} (hR : (R : EReal) < f x) :
    ∃ u : Fin n → ℝ, ∃ β : ℝ,
      R ≤ β + x ⬝ᵥ u ∧ ∀ y, ((β + y ⬝ᵥ u : ℝ) : EReal) ≤ f y := by
  classical
  let z : (Fin n → ℝ) × ℝ := (x, R)
  have hz : z ∉ epigraph Set.univ f := fun h => (not_le_of_gt hR) h.2
  obtain ⟨l, q, hl, hlz⟩ := geometric_hahn_banach_closed_point hf.1
    (isClosed_epigraph hlsc) hz
  obtain ⟨a, ha⟩ := continuousLinear_prod_decomp l
  let c : ℝ := l (0, 1)
  have hc : c ≤ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨p, hp⟩ := hf.2.1
    let T : ℝ := max 0 ((q - (p.1 ⬝ᵥ a + p.2 * c)) / c) + 1
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hpT : (p.1, p.2 + T) ∈ epigraph Set.univ f :=
      ⟨trivial, hp.2.trans (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right hT))⟩
    have hbound := hl _ hpT
    have hcalc : q < l (p.1, p.2 + T) := by
      rw [ha p.1 (p.2 + T)]
      change q < p.1 ⬝ᵥ a + (p.2 + T) * c
      dsimp only [T]
      have hmax : (q - (p.1 ⬝ᵥ a + p.2 * c)) / c ≤
          max 0 ((q - (p.1 ⬝ᵥ a + p.2 * c)) / c) := le_max_right _ _
      have hmul := mul_le_mul_of_nonneg_right hmax h.le
      have hdiv : ((q - (p.1 ⬝ᵥ a + p.2 * c)) / c) * c =
          q - (p.1 ⬝ᵥ a + p.2 * c) := div_mul_cancel₀ _ h.ne'
      nlinarith
    exact (not_lt_of_ge hbound.le) hcalc
  by_cases hc0 : c = 0
  · obtain ⟨u₀, β₀, hbase⟩ := exists_affineMinorant hlsc hf
    have hax : q < x ⬝ᵥ a := by
      have := hlz
      dsimp [z] at this
      rw [ha] at this
      simp [c, hc0] at this
      exact this
    let T : ℝ := max 0 ((R - (β₀ + x ⬝ᵥ u₀)) / (x ⬝ᵥ a - q)) + 1
    have hgap : 0 < x ⬝ᵥ a - q := sub_pos.mpr hax
    have hT : 0 ≤ T := by dsimp [T]; positivity
    let u : Fin n → ℝ := u₀ + T • a
    let β : ℝ := β₀ - T * q
    refine ⟨u, β, ?_, fun y => ?_⟩
    · dsimp [u, β]
      rw [dotProduct_add, dotProduct_smul]
      simp only [smul_eq_mul]
      have hmax : (R - (β₀ + x ⬝ᵥ u₀)) / (x ⬝ᵥ a - q) ≤
          max 0 ((R - (β₀ + x ⬝ᵥ u₀)) / (x ⬝ᵥ a - q)) := le_max_right _ _
      have hmul := mul_le_mul_of_nonneg_right hmax hgap.le
      field_simp [ne_of_gt hgap] at hmul
      nlinarith
    · by_cases hytop : f y = ⊤
      · rw [hytop]; exact le_top
      have hybot := hf.2.2 y trivial
      lift f y to ℝ using ⟨hytop, hybot⟩ with s hs
      have hyepi : (y, s) ∈ epigraph Set.univ f := ⟨trivial, by rw [← hs]⟩
      have hay : y ⬝ᵥ a < q := by
        have := hl _ hyepi
        rw [ha] at this
        simpa [c, hc0] using this
      have hbase' : β₀ + y ⬝ᵥ u₀ ≤ s := by
        have := hbase y
        rw [← hs] at this
        exact EReal.coe_le_coe_iff.mp this
      apply EReal.coe_le_coe_iff.mpr
      dsimp [u, β]
      rw [dotProduct_add, dotProduct_smul]
      simp only [smul_eq_mul]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hT (sub_nonpos.mpr hay.le)]
  · have hcneg : c < 0 := lt_of_le_of_ne hc hc0
    let u : Fin n → ℝ := fun i => -a i / c
    let β : ℝ := R + x ⬝ᵥ a / c
    refine ⟨u, β, ?_, fun y => ?_⟩
    · dsimp [u, β]
      have hdot : x ⬝ᵥ (fun i => -a i / c) = -(x ⬝ᵥ a) / c := by
        simp only [dotProduct]
        rw [eq_div_iff hc0, Finset.sum_mul, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by field_simp [hc0]
      rw [hdot]
      have hxdiv : x ⬝ᵥ a / c + (-(x ⬝ᵥ a)) / c = 0 := by
        rw [← add_div]
        simp
      linarith
    · by_cases hytop : f y = ⊤
      · rw [hytop]; exact le_top
      have hybot := hf.2.2 y trivial
      lift f y to ℝ using ⟨hytop, hybot⟩ with s hs
      have hyepi : (y, s) ∈ epigraph Set.univ f := ⟨trivial, by rw [← hs]⟩
      have hxy := (hl _ hyepi).trans hlz
      dsimp [z] at hxy
      rw [ha y s, ha x R] at hxy
      apply EReal.coe_le_coe_iff.mpr
      dsimp [u, β]
      have hdot : y ⬝ᵥ (fun i => -a i / c) = -(y ⬝ᵥ a) / c := by
        simp only [dotProduct]
        rw [eq_div_iff hc0, Finset.sum_mul, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by field_simp [hc0]
      rw [hdot]
      apply le_of_lt
      by_contra hn
      push_neg at hn
      have hmul := mul_le_mul_of_nonpos_right hn hc
      have hxdiv : (x ⬝ᵥ a / c) * c = x ⬝ᵥ a := div_mul_cancel₀ _ hc0
      have hydiv : (-(y ⬝ᵥ a) / c) * c = -(y ⬝ᵥ a) := div_mul_cancel₀ _ hc0
      nlinarith

/-- Every affine minorant of `f` lies below its biconjugate. -/
lemma affineMinorant_le_biconjugate {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn Set.univ f) {u : Fin n → ℝ} {β : ℝ}
    (hminor : ∀ y, ((β + y ⬝ᵥ u : ℝ) : EReal) ≤ f y) (x : Fin n → ℝ) :
    ((β + x ⬝ᵥ u : ℝ) : EReal) ≤ fenchelConjugate n (fenchelConjugate n f) x := by
  have hutop : fenchelConjugate n f u ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top (-β)) (fenchelConjugate_le_of_affineMinorant hminor)
  have hubot := fenchelConjugate_ne_bot_of_proper hf u
  lift fenchelConjugate n f u to ℝ using ⟨hutop, hubot⟩ with r hrs
  have hrle : r ≤ -β := by
    have h := fenchelConjugate_le_of_affineMinorant hminor
    rw [← hrs] at h
    exact EReal.coe_le_coe_iff.mp h
  calc
    ((β + x ⬝ᵥ u : ℝ) : EReal) ≤ ((x ⬝ᵥ u - r : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by linarith)
    _ = ((x ⬝ᵥ u : ℝ) : EReal) - fenchelConjugate n f u := by rw [← hrs]; rfl
    _ ≤ fenchelConjugate n (fenchelConjugate n f) x := by
      rw [fenchelConjugate_eq_iSup n (fenchelConjugate n f)]
      calc
        ((x ⬝ᵥ u : ℝ) : EReal) - fenchelConjugate n f u =
            ((u ⬝ᵥ x : ℝ) : EReal) - fenchelConjugate n f u := by
              rw [dotProduct_comm x u]
        _ ≤ ⨆ y : Fin n → ℝ, ((y ⬝ᵥ x : ℝ) : EReal) - fenchelConjugate n f y :=
          le_iSup (fun y : Fin n → ℝ =>
            ((y ⬝ᵥ x : ℝ) : EReal) - fenchelConjugate n f y) u

/-- The biconjugate never exceeds a proper function. -/
lemma fenchelConjugate_fenchelConjugate_le {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ) :
    fenchelConjugate n (fenchelConjugate n f) x ≤ f x := by
  by_cases hxtop : f x = ⊤
  · rw [hxtop]
    exact le_top
  have hxbot := hf.2.2 x trivial
  lift f x to ℝ using ⟨hxtop, hxbot⟩ with r hr
  rw [fenchelConjugate_eq_iSup]
  refine iSup_le fun u => ?_
  have hubot := fenchelConjugate_ne_bot_of_proper hf u
  by_cases hutop : fenchelConjugate n f u = ⊤
  · simp [hutop]
  lift fenchelConjugate n f u to ℝ using ⟨hutop, hubot⟩ with s hs
  have hxu : x ⬝ᵥ u - r ≤ s := by
    have h := le_iSup (fun y : Fin n → ℝ => ((y ⬝ᵥ u : ℝ) : EReal) - f y) x
    rw [← fenchelConjugate_eq_iSup, ← hr, ← hs, ← EReal.coe_sub] at h
    exact EReal.coe_le_coe_iff.mp h
  rw [← EReal.coe_sub]
  simp only [dotProduct_comm u x]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Finite-dimensional Fenchel–Moreau for lower-semicontinuous proper convex functions. -/
theorem fenchelConjugate_biconjugate {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hlsc : LowerSemicontinuous f) (hf : ProperConvexFunctionOn Set.univ f) :
    fenchelConjugate n (fenchelConjugate n f) = f := by
  funext x
  apply le_antisymm (fenchelConjugate_fenchelConjugate_le hf x)
  have hlevel : ∀ R : ℝ, (R : EReal) < f x →
      (R : EReal) ≤ fenchelConjugate n (fenchelConjugate n f) x := by
    intro R hR
    obtain ⟨u, β, hx, hminor⟩ := exists_affineMinorant_gt hlsc hf hR
    exact (EReal.coe_le_coe_iff.mpr hx).trans (affineMinorant_le_biconjugate hf hminor x)
  by_cases hxtop : f x = ⊤
  · rw [hxtop]
    have hbi : fenchelConjugate n (fenchelConjugate n f) x = ⊤ :=
      (EReal.eq_top_iff_forall_lt _).2 fun R =>
        lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith))
          (hlevel (R + 1) (by rw [hxtop]; exact EReal.coe_lt_top _))
    rw [hbi]
  have hxbot := hf.2.2 x trivial
  lift f x to ℝ using ⟨hxtop, hxbot⟩ with r hr
  have hbi_le : fenchelConjugate n (fenchelConjugate n f) x ≤ (r : EReal) := by
    rw [hr]
    exact fenchelConjugate_fenchelConjugate_le hf x
  have hbi_top : fenchelConjugate n (fenchelConjugate n f) x ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top r) hbi_le
  have hbi_bot : fenchelConjugate n (fenchelConjugate n f) x ≠ ⊥ := by
    have h := hlevel (r - 1) (EReal.coe_lt_coe_iff.mpr (by linarith))
    exact fun hb => EReal.coe_ne_bot (r - 1) (le_bot_iff.mp (hb ▸ h))
  lift fenchelConjugate n (fenchelConjugate n f) x to ℝ
    using ⟨hbi_top, hbi_bot⟩ with s hs
  apply EReal.coe_le_coe_iff.mpr
  apply le_of_forall_lt
  intro R hR
  have h := hlevel ((R + r) / 2)
    (EReal.coe_lt_coe_iff.mpr (by linarith))
  have hrs : (R + r) / 2 ≤ s := EReal.coe_le_coe_iff.mp h
  linarith

end GHS
