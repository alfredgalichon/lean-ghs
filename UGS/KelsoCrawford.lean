import UGS.Submodularity3

/-!
# Kelso--Crawford is already unified on subdifferentials

`UGS/KCCounterexample.lean` shows that the Kelso--Crawford substitutes property
is strictly weaker than unified gross substitutes for correspondences at large.
This file shows that the gap **closes** on the class of subdifferentials of
finite convex functions: for `Q = ∂f` with `f : (Fin n → ℝ) → ℝ` finite convex,

* `Submodular f`,
* `IsUGS (subdiffCorr f)`,
* `KCsubstitutes (subdiffCorr f)`,
* `KCsingle f` — Kelso--Crawford for price pairs differing in a *single*
  coordinate, and only one of its two clauses,

are all equivalent (`tfae_submodular_isUGS_kc`). This is `prop:KCsub` of the
self-lecture; with `Submodular ↔ IsUGS` (GSV Theorem 3, `Submodularity3.lean`)
it says that the Ausubel--Milgrom characterization survives the weakening of UGS
to Kelso--Crawford.

## The mathematical point

GSV's route from a substitutes hypothesis to submodularity passes through the
directional-derivative inequality `DD` of `submodular_of_dderiv`,
`f'(p; b^≤) + f'(p'; b^>) ≤ f'(p ⊓ p'; b)`, which compares two *different* base
points against one meet witness — exactly the "unification" Kelso--Crawford does
not supply. The observation here is that the fencing argument behind
`submodular_of_dderiv` never needs the joint statement: it only ever compares
`f'(·; b)` in one fixed direction `b ≥ 0` at two *comparable* base points that
agree on the support of `b` (`dirMono` below). That comparison follows from one
Kelso--Crawford clause, because a subgradient attaining `f'(y; b)`
(`exists_subgrad_achieving`) is dominated on the support of `b` by some
subgradient at `x`, which in turn is dominated by `f'(x; b)`
(`subgrad_le_dderiv`).

Nothing here needs `f` differentiable anywhere: attainment plays the role that
a.e. differentiability plays in the informal argument.
-/

open Matrix

namespace Correspondence

variable {n : ℕ}

/-- The `j`-th unit vector of `Fin n → ℝ`, the direction of a single-coordinate
price change. -/
def unitVec (j : Fin n) : Fin n → ℝ := Pi.single j 1

theorem unitVec_self (j : Fin n) : unitVec j j = 1 := by simp [unitVec]

theorem unitVec_of_ne {j z : Fin n} (h : z ≠ j) : unitVec j z = 0 := by
  simp [unitVec, Pi.single_eq_of_ne h]

/-- **Kelso--Crawford substitutes, single-coordinate form.** Only price pairs
differing in one coordinate are compared, and only one of the two Kelso--Crawford
clauses is imposed: whenever `q` is supplied at the higher price `p + s • e j`,
some `q'` supplied at `p` dominates it on every coordinate other than `j`. -/
def KCsingle (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (p : Fin n → ℝ) (j : Fin n) (s : ℝ), 0 < s →
    ∀ q, SubgradVec f (p + s • unitVec j) q →
      ∃ q', SubgradVec f p q' ∧ ∀ z, z ≠ j → q z ≤ q' z

/-- The Kelso--Crawford property of the subdifferential correspondence
specializes to its single-coordinate form. -/
theorem KCsingle_of_KCsubstitutes (f : (Fin n → ℝ) → ℝ)
    (hKC : KCsubstitutes (subdiffCorr f)) : KCsingle f := by
  intro p j s hs q hq
  have hle : p ≤ p + s • unitVec j := by
    intro z
    rcases eq_or_ne z j with rfl | hz
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec_self, mul_one]
      linarith
    · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec_of_ne hz]
  obtain ⟨q', hq', hdom⟩ := hKC (p + s • unitVec j) p hle q hq
  refine ⟨q', hq', fun z hz => hdom z ?_⟩
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec_of_ne hz]

/-! ## From Kelso--Crawford to monotone directional derivatives -/

/-- **One step.** Raising a single price `j` does not raise the directional
derivative in any nonnegative direction `b` that ignores coordinate `j`.
The subgradient attaining `f'(w + s•e j; b)` is dominated off `j` by some
subgradient at `w`, which is dominated by `f'(w; b)`. -/
theorem dderiv_step_of_KCsingle (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (hKC : KCsingle f)
    (w : Fin n → ℝ) (j : Fin n) {s : ℝ} (hs : 0 < s) (b : Fin n → ℝ)
    (hb : 0 ≤ b) (hbj : b j = 0) :
    dderiv f (w + s • unitVec j) b ≤ dderiv f w b := by
  obtain ⟨q, hqsub, hq⟩ := exists_subgrad_achieving f hconv (w + s • unitVec j) b
  obtain ⟨q', hq'sub, hdom⟩ := hKC w j s hs q hqsub
  have hdot : q ⬝ᵥ b ≤ q' ⬝ᵥ b := by
    apply Finset.sum_le_sum
    intro z _
    rcases eq_or_ne z j with rfl | hz
    · simp [hbj]
    · exact mul_le_mul_of_nonneg_right (hdom z hz) (hb z)
  calc dderiv f (w + s • unitVec j) b = q ⬝ᵥ b := hq
    _ ≤ q' ⬝ᵥ b := hdot
    _ ≤ dderiv f w b := subgrad_le_dderiv f hconv hq'sub b

/-- Induction over the finite set of coordinates on which `x` and `y` may
differ: the one-step comparison chains along a coordinate path from `x` to `y`. -/
private theorem dirMono_aux (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (hKC : KCsingle f)
    {b : Fin n → ℝ} (hb : 0 ≤ b) :
    ∀ (S : Finset (Fin n)) (x y : Fin n → ℝ), x ≤ y → (∀ z, z ∉ S → x z = y z) →
      (∀ z, b z ≠ 0 → x z = y z) → dderiv f y b ≤ dderiv f x b := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro x y _ hoff _
      have hxy : x = y := funext fun z => hoff z (Finset.notMem_empty z)
      rw [hxy]
  | insert j S hjS ih =>
      intro x y hxy hoff hagree
      classical
      set x' : Fin n → ℝ := fun z => if z = j then y z else x z with hx'def
      have hx'j : x' j = y j := by simp [hx'def]
      have hx'ne : ∀ z, z ≠ j → x' z = x z := by
        intro z hz; simp [hx'def, hz]
      have hx'y : x' ≤ y := by
        intro z
        rcases eq_or_ne z j with rfl | hz
        · exact le_of_eq hx'j
        · rw [hx'ne z hz]; exact hxy z
      have hoff' : ∀ z, z ∉ S → x' z = y z := by
        intro z hz
        rcases eq_or_ne z j with rfl | hzj
        · exact hx'j
        · rw [hx'ne z hzj]
          exact hoff z (by simp [Finset.mem_insert, hzj, hz])
      have hagree' : ∀ z, b z ≠ 0 → x' z = y z := by
        intro z hz
        rcases eq_or_ne z j with rfl | hzj
        · exact hx'j
        · rw [hx'ne z hzj]; exact hagree z hz
      have hIH := ih x' y hx'y hoff' hagree'
      rcases eq_or_lt_of_le (hxy j) with heq | hlt
      · have hxx' : x' = x := by
          funext z
          rcases eq_or_ne z j with rfl | hz
          · rw [hx'j, ← heq]
          · exact hx'ne z hz
        rwa [hxx'] at hIH
      · have hbj : b j = 0 := by
          by_contra hbj
          exact absurd (hagree j hbj) (ne_of_lt hlt)
        have hstep :=
          dderiv_step_of_KCsingle f hconv hKC x j (sub_pos.mpr hlt) b hb hbj
        have hxeq : x + (y j - x j) • unitVec j = x' := by
          funext z
          rcases eq_or_ne z j with rfl | hz
          · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec_self, hx'j]
          · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec_of_ne hz, hx'ne z hz]
        rw [hxeq] at hstep
        exact hIH.trans hstep

/-- **`dirMono`.** Under Kelso--Crawford, the directional derivative in a fixed
nonnegative direction `b` is antitone in the base point along price increases
that leave the support of `b` untouched. -/
theorem dirMono_of_KCsingle (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (hKC : KCsingle f)
    {x y b : Fin n → ℝ} (hb : 0 ≤ b) (hxy : x ≤ y)
    (hagree : ∀ z, b z ≠ 0 → x z = y z) :
    dderiv f y b ≤ dderiv f x b :=
  dirMono_aux f hconv hKC hb Finset.univ x y hxy
    (fun z hz => absurd (Finset.mem_univ z) hz) hagree

/-! ## From monotone directional derivatives to submodularity -/

/-- **Submodularity by fencing, from `dirMono` alone.** With `b = (p'-p)⁺`, the
function `φ(t) = f(p + t•b) - f(p⊓p' + t•b)` is nonincreasing on `[0,1]`: its
right derivative is `≤ 0` because the two base points `p⊓p' + t•b ≤ p + t•b`
agree on the support of `b`. Then `φ(1) ≤ φ(0)` is submodularity.

This is the variant of `submodular_of_dderiv` that avoids the joint (unified)
hypothesis `DD`. -/
theorem submodular_of_dirMono (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hDM : ∀ x y b : Fin n → ℝ, 0 ≤ b → x ≤ y → (∀ z, b z ≠ 0 → x z = y z) →
      dderiv f y b ≤ dderiv f x b) :
    Submodular f := by
  intro p p'
  set b : Fin n → ℝ := (p' - p) ⊔ 0 with hbdef
  have hb0 : (0 : Fin n → ℝ) ≤ b := hbdef ▸ le_sup_right
  have hbz0 : ∀ z, p z ≤ p' z → b z = p' z - p z := by
    intro z h; simp only [hbdef, Pi.sup_apply, Pi.sub_apply, Pi.zero_apply]
    exact sup_eq_left.mpr (by linarith)
  have hbz0' : ∀ z, p' z < p z → b z = 0 := by
    intro z h; simp only [hbdef, Pi.sup_apply, Pi.sub_apply, Pi.zero_apply]
    exact sup_eq_right.mpr (by linarith)
  set A : ℝ → ℝ := fun t => f (p + t • b) with hA
  set C : ℝ → ℝ := fun t => f (p ⊓ p' + t • b) with hC
  have hAconv := convexOn_shift f hconv p b
  have hCconv := convexOn_shift f hconv (p ⊓ p') b
  have hAcont : ContinuousOn A (Set.Icc (0:ℝ) 1) :=
    (hAconv.continuousOn isOpen_univ).mono (Set.subset_univ _)
  have hCcont : ContinuousOn C (Set.Icc (0:ℝ) 1) :=
    (hCconv.continuousOn isOpen_univ).mono (Set.subset_univ _)
  have hDA : ∀ x, HasDerivWithinAt A (derivWithin A (Set.Ioi x) x) (Set.Ici x) x := by
    intro x
    have hx : x ∈ interior (Set.univ : Set ℝ) := by rw [interior_univ]; trivial
    exact ((hAconv.hasDerivWithinAt_sInf_slope_of_mem_interior
      hx).differentiableWithinAt.hasDerivWithinAt).Ici_of_Ioi
  have hDC : ∀ x, HasDerivWithinAt C (derivWithin C (Set.Ioi x) x) (Set.Ici x) x := by
    intro x
    have hx : x ∈ interior (Set.univ : Set ℝ) := by rw [interior_univ]; trivial
    exact ((hCconv.hasDerivWithinAt_sInf_slope_of_mem_interior
      hx).differentiableWithinAt.hasDerivWithinAt).Ici_of_Ioi
  -- the bound: `derivWithin A ≤ derivWithin C`, from `dirMono` at the shifted points
  have hbound : ∀ x ∈ Set.Ico (0:ℝ) 1,
      derivWithin A (Set.Ioi x) x - derivWithin C (Set.Ioi x) x ≤ 0 := by
    rintro x -
    have hle : p ⊓ p' + x • b ≤ p + x • b := by
      intro z
      have h : (p ⊓ p') z ≤ p z := (inf_le_left : p ⊓ p' ≤ p) z
      simp only [Pi.add_apply]
      linarith
    have hagree : ∀ z, b z ≠ 0 → (p ⊓ p' + x • b) z = (p + x • b) z := by
      intro z hz
      have hpz : p z ≤ p' z := by
        by_contra h
        exact hz (hbz0' z (not_le.mp h))
      simp only [Pi.add_apply, Pi.inf_apply, inf_of_le_left hpz]
    have key := hDM (p ⊓ p' + x • b) (p + x • b) b hb0 hle hagree
    rw [dderiv_shift f p b x, dderiv_shift f (p ⊓ p') b x] at key
    have key' : derivWithin A (Set.Ioi x) x ≤ derivWithin C (Set.Ioi x) x := key
    linarith
  have hfence := image_le_of_deriv_right_le_deriv_boundary
    (f := fun t => A t - C t) (a := 0) (b := 1) (hAcont.sub hCcont)
    (f' := fun x => derivWithin A (Set.Ioi x) x - derivWithin C (Set.Ioi x) x)
    (fun x _ => (hDA x).sub (hDC x))
    (B := fun _ => A 0 - C 0) (B' := fun _ => 0) (le_refl _)
    continuousOn_const (fun x _ => hasDerivWithinAt_const x _ _) hbound
  have hφ1 := hfence (Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩)
  have hpb : p + (1:ℝ) • b = p ⊔ p' := by
    funext z; simp only [Pi.add_apply, Pi.sup_apply, one_smul]
    by_cases h : p z ≤ p' z
    · rw [hbz0 z h, sup_of_le_right h]; ring
    · have hlt := not_le.mp h
      rw [hbz0' z hlt, sup_of_le_left hlt.le, add_zero]
  have hmpb : p ⊓ p' + (1:ℝ) • b = p' := by
    funext z; simp only [Pi.add_apply, Pi.inf_apply, one_smul]
    by_cases h : p z ≤ p' z
    · rw [hbz0 z h, inf_of_le_left h]; ring
    · have hlt := not_le.mp h
      rw [hbz0' z hlt, inf_of_le_right hlt.le, add_zero]
  have hA0 : A 0 = f p := by simp only [hA, zero_smul, add_zero]
  have hA1 : A 1 = f (p ⊔ p') := by simp only [hA]; rw [hpb]
  have hC0 : C 0 = f (p ⊓ p') := by simp only [hC, zero_smul, add_zero]
  have hC1 : C 1 = f p' := by simp only [hC]; rw [hmpb]
  simp only [hA0, hA1, hC0, hC1] at hφ1
  linarith [hφ1]

/-! ## The equivalence -/

/-- **`prop:KCsub`.** For the subdifferential of a finite convex function on
`Fin n → ℝ`, submodularity, unified gross substitutes, Kelso--Crawford
substitutes, and the single-coordinate one-clause form of Kelso--Crawford are all
equivalent. -/
theorem tfae_submodular_isUGS_kc (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) :
    List.TFAE
      [Submodular f, IsUGS (subdiffCorr f), KCsubstitutes (subdiffCorr f), KCsingle f] := by
  tfae_have 1 → 2 := fun h => (submodular_iff_isUGS_subdiff f hconv).mp h
  tfae_have 2 → 3 := fun h => h.kc (fun p => subdiff_nonempty f hconv p)
  tfae_have 3 → 4 := fun h => KCsingle_of_KCsubstitutes f h
  tfae_have 4 → 1 := fun h =>
    submodular_of_dirMono f hconv
      (fun _ _ _ hb hxy hagree => dirMono_of_KCsingle f hconv h hb hxy hagree)
  tfae_finish

/-- The Ausubel--Milgrom characterization under the *weaker* Kelso--Crawford
hypothesis: for a finite convex `f`, `∂f` satisfies Kelso--Crawford substitutes
iff `f` is submodular (hence iff `∂f` satisfies unified gross substitutes). -/
theorem submodular_iff_KCsubstitutes_subdiff (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) :
    Submodular f ↔ KCsubstitutes (subdiffCorr f) :=
  (tfae_submodular_isUGS_kc f hconv).out 0 2

/-! ## The mirror image: the other Kelso--Crawford clause

Property 1 of the note has two clauses, and `KCsingle`/`KCsubstitutes` above are
clause (b) (from the higher price down). Clause (a) --- from the lower price up,
which is the form Kelso and Crawford state and the form a gross-substitutes
valuation delivers --- gives the same conclusions, through the reflection
`f(-p)`: it swaps meet and join, hence preserves submodularity, and turns each
clause into the other. -/

/-- The reflection `p ↦ f(-p)`. -/
def reflect (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ := fun p => f (-p)

theorem reflect_reflect (f : (Fin n → ℝ) → ℝ) : reflect (reflect f) = f := by
  funext p; simp [reflect]

theorem convexOn_reflect (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) :
    ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (reflect f) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h : -(a • x + b • y) = a • (-x) + b • (-y) := by
    funext z
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [reflect, h]
  exact hconv.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem submodular_reflect {f : (Fin n → ℝ) → ℝ} (h : Submodular f) :
    Submodular (reflect f) := by
  intro p p'
  have h1 : -(p ⊓ p') = (-p) ⊔ (-p') := by
    funext z; simp only [Pi.neg_apply, Pi.inf_apply, Pi.sup_apply]; exact neg_inf _ _
  have h2 : -(p ⊔ p') = (-p) ⊓ (-p') := by
    funext z; simp only [Pi.neg_apply, Pi.inf_apply, Pi.sup_apply]; exact neg_sup _ _
  simp only [reflect, h1, h2]
  linarith [h (-p) (-p')]

theorem subgradVec_reflect (f : (Fin n → ℝ) → ℝ) (p q : Fin n → ℝ) :
    SubgradVec (reflect f) p q ↔ SubgradVec f (-p) (-q) := by
  have hd : ∀ x : Fin n → ℝ, (-q) ⬝ᵥ (x - -p) = q ⬝ᵥ (-x - p) := by
    intro x
    simp only [dotProduct, Pi.neg_apply, Pi.sub_apply]
    exact Finset.sum_congr rfl fun z _ => by ring
  constructor
  · intro h x
    have hx := h (-x)
    rw [hd x]
    simpa only [reflect, neg_neg] using hx
  · intro h x
    have hx := h (-x)
    rw [hd (-x)] at hx
    simpa only [reflect, neg_neg] using hx

theorem dderiv_reflect (f : (Fin n → ℝ) → ℝ) (p b : Fin n → ℝ) :
    dderiv (reflect f) p b = dderiv f (-p) (-b) := by
  have h : (fun t : ℝ => reflect f (p + t • b)) = (fun t : ℝ => f (-p + t • (-b))) := by
    funext t
    simp only [reflect]
    congr 1
    funext z
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dderiv, dderiv, h]

/-- **Mirror-image fencing.** The directional-monotonicity hypothesis read in the
directions `-b` --- equivalently, on the *smallest* rather than the largest
subgradient in direction `b` --- also gives submodularity. -/
theorem submodular_of_dirMonoA (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hDM : ∀ x y b : Fin n → ℝ, 0 ≤ b → x ≤ y → (∀ z, b z ≠ 0 → x z = y z) →
      dderiv f x (-b) ≤ dderiv f y (-b)) :
    Submodular f := by
  have hg : Submodular (reflect f) := by
    refine submodular_of_dirMono (reflect f) (convexOn_reflect f hconv) ?_
    intro x' y' b hb hxy hagree
    rw [dderiv_reflect, dderiv_reflect]
    refine hDM (-y') (-x') b hb (neg_le_neg hxy) ?_
    intro z hz
    have := hagree z hz
    simp only [Pi.neg_apply]
    linarith
  have := submodular_reflect hg
  rwa [reflect_reflect] at this

/-- Clause (a), single-coordinate form. -/
def KCsingleA (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (p : Fin n → ℝ) (j : Fin n) (s : ℝ), 0 < s →
    ∀ q, SubgradVec f p q →
      ∃ q', SubgradVec f (p + s • unitVec j) q' ∧ ∀ z, z ≠ j → q' z ≤ q z

/-- A submodular finite convex function satisfies clause (a) as well. -/
theorem KCsubstitutesA_subdiff_of_submodular (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (hsub : Submodular f) :
    KCsubstitutesA (subdiffCorr f) := by
  intro p p' hpp' q' hq'
  -- `hpp' : p' ≤ p`, `q'` sits at the lower price `p'`; produce one at `p`.
  have hKC : KCsubstitutes (subdiffCorr (reflect f)) :=
    ((tfae_submodular_isUGS_kc (reflect f) (convexOn_reflect f hconv)).out 0 2).mp
      (submodular_reflect hsub)
  have hq2 : subdiffCorr (reflect f) (-p') (-q') := by
    show SubgradVec (reflect f) (-p') (-q')
    rw [subgradVec_reflect]
    simpa only [neg_neg] using hq'
  obtain ⟨q'', hq''mem, hdom⟩ := hKC (-p') (-p) (neg_le_neg hpp') (-q') hq2
  refine ⟨-q'', ?_, ?_⟩
  · show SubgradVec f p (-q'')
    have h := (subgradVec_reflect f (-p) q'').mp hq''mem
    simpa only [neg_neg] using h
  · intro z hz
    have h := hdom z (by simp only [Pi.neg_apply, hz])
    simp only [Pi.neg_apply] at h ⊢
    linarith

/-- Clause (a) in its weakest form also characterizes submodularity. -/
theorem submodular_of_KCsingleA (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (h : KCsingleA f) :
    Submodular f := by
  have hg : Submodular (reflect f) := by
    refine ((tfae_submodular_isUGS_kc (reflect f) (convexOn_reflect f hconv)).out 3 0).mp ?_
    intro p j s hs q hq
    have hq2 : SubgradVec f (-(p + s • unitVec j)) (-q) := (subgradVec_reflect f _ q).mp hq
    obtain ⟨r', hr'mem, hr'dom⟩ := h (-(p + s • unitVec j)) j s hs (-q) hq2
    have hshift : -(p + s • unitVec j) + s • unitVec j = -p := by
      funext z
      simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hshift] at hr'mem
    refine ⟨-r', ?_, ?_⟩
    · rw [subgradVec_reflect]
      simpa only [neg_neg] using hr'mem
    · intro z hz
      have h' := hr'dom z hz
      simp only [Pi.neg_apply] at h' ⊢
      linarith
  have := submodular_reflect hg
  rwa [reflect_reflect] at this

/-- Non-vacuity of the hypothesis: a constant (hence submodular) function does
satisfy `KCsingle`, so `4 → 1` above is not an implication from an empty class. -/
example : KCsingle (fun _ : Fin n → ℝ => (0:ℝ)) := by
  have hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun _ => (0:ℝ)) :=
    convexOn_const 0 convex_univ
  have hsub : Submodular (fun _ : Fin n → ℝ => (0:ℝ)) := fun _ _ => by norm_num
  exact ((tfae_submodular_isUGS_kc _ hconv).out 0 3).mp hsub

/-- Kelso--Crawford substitutes for `∂f` implies unified gross substitutes for
`∂f` — the gap of `UGS/KCCounterexample.lean` closes on subdifferentials. -/
theorem isUGS_subdiff_of_KCsubstitutes (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hKC : KCsubstitutes (subdiffCorr f)) : IsUGS (subdiffCorr f) :=
  ((tfae_submodular_isUGS_kc f hconv).out 2 1).mp hKC

end Correspondence
