import GHS.Theorem4
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# GHS Example 2: quadratic costs — exchangeable ⟺ inverse Stieltjes

Roadmap item 19: the quadratic instance of Theorem 2.  For a symmetric
positive-semidefinite `A` with two-sided inverse `B`, the quadratic cost
`c(q) = ½ qᵀAq` is exchangeable **iff** the off-diagonal entries of
`B = A⁻¹` are nonpositive — i.e. iff `A` is an inverse Stieltjes-type
matrix.  Machine-checked chain:

* `quadForm_inf_sup` — the exact lattice identity
  `Q(x⊓y) + Q(x⊔y) = Q(x) + Q(y) + (x-y)⁺ᵀ A (x-y)⁻` (the diagonal drops
  because `{(x⊓y)ᵢ,(x⊔y)ᵢ} = {xᵢ,yᵢ}`; only the cross terms between the
  disjointly-supported parts survive);
* `submodular_quadForm_iff` — a symmetric quadratic form is submodular iff
  its off-diagonal entries are nonpositive (test vectors `eᵢ, eⱼ` for
  necessity; pointwise complementarity `x⁺ᵢ x⁻ᵢ = 0` for sufficiency);
* `fenchelConjugate_quadForm` — `(½ qᵀAq)* = ½ pᵀBp` by completing the
  square (attainment at `q* = Bp`; only positive **semi**definiteness is
  needed);
* `exchangeable_quadForm_iff_offdiag_inv` — **Example 2**: assembling the
  above through Claim 1 (`qOrderE_iff_pOrderE_fenchelConjugate`).

Combined with the classical M-matrix theory (see the
unified-gross-substitutes lecture), the condition "`B = A⁻¹` symmetric PSD
with nonpositive off-diagonals" says exactly that `A` is the inverse of a
Stieltjes-type matrix.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set Matrix

namespace GHS

variable {n : ℕ}

/-- The quadratic form `½ vᵀMv`. -/
noncomputable def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ℝ :=
  v ⬝ᵥ (M *ᵥ v) / 2

/-! ## Bilinear calculus -/

theorem bilin_comm {M : Matrix (Fin n) (Fin n) ℝ} (hsym : Mᵀ = M)
    (v w : Fin n → ℝ) : v ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : M j i = M i j := congrFun (congrFun hsym i) j
  rw [h]
  ring

theorem quadForm_add {M : Matrix (Fin n) (Fin n) ℝ} (hsym : Mᵀ = M)
    (v w : Fin n → ℝ) :
    quadForm M (v + w) = quadForm M v + quadForm M w + v ⬝ᵥ (M *ᵥ w) := by
  have hcomm := bilin_comm hsym w v
  simp only [quadForm, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  linarith

theorem quadForm_sub {M : Matrix (Fin n) (Fin n) ℝ} (hsym : Mᵀ = M)
    (v w : Fin n → ℝ) :
    quadForm M (v - w) = quadForm M v + quadForm M w - v ⬝ᵥ (M *ᵥ w) := by
  have h := quadForm_add hsym (v - w) w
  rw [sub_add_cancel] at h
  have h2 : (v - w) ⬝ᵥ (M *ᵥ w) = v ⬝ᵥ (M *ᵥ w) - w ⬝ᵥ (M *ᵥ w) :=
    sub_dotProduct _ _ _
  have h3 : w ⬝ᵥ (M *ᵥ w) = 2 * quadForm M w := by
    rw [quadForm]
    ring
  linarith

theorem quadForm_smul {M : Matrix (Fin n) (Fin n) ℝ} (c : ℝ)
    (v : Fin n → ℝ) : quadForm M (c • v) = c ^ 2 * quadForm M v := by
  simp only [quadForm, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

theorem quadForm_zero (M : Matrix (Fin n) (Fin n) ℝ) : quadForm M 0 = 0 := by
  simp [quadForm]

/-! ## The lattice identity and submodularity -/

theorem inf_add_posPart (x y : Fin n → ℝ) : x ⊓ y + (x - y)⁺ = x := by
  funext i
  show (x ⊓ y) i + ((x - y) i)⁺ = x i
  rw [Pi.inf_apply]
  rcases le_total (x i) (y i) with h | h
  · rw [inf_eq_left.mpr h, posPart_of_nonpos (by show x i - y i ≤ 0; linarith)]
    ring
  · rw [inf_eq_right.mpr h, posPart_of_nonneg (by show (0:ℝ) ≤ x i - y i; linarith)]
    show y i + (x i - y i) = x i
    ring

theorem inf_add_negPart (x y : Fin n → ℝ) : x ⊓ y + (x - y)⁻ = y := by
  funext i
  show (x ⊓ y) i + ((x - y) i)⁻ = y i
  rw [Pi.inf_apply]
  rcases le_total (x i) (y i) with h | h
  · rw [inf_eq_left.mpr h]
    rw [negPart_eq_neg.mpr (by show x i - y i ≤ 0; linarith)]
    show x i + -(x i - y i) = y i
    ring
  · rw [inf_eq_right.mpr h]
    rw [negPart_eq_zero.mpr (by show (0:ℝ) ≤ x i - y i; linarith)]
    ring

theorem sup_eq_inf_add_parts (x y : Fin n → ℝ) :
    x ⊔ y = x ⊓ y + (x - y)⁺ + (x - y)⁻ := by
  funext i
  show max (x i) (y i) = min (x i) (y i) + (x i - y i)⁺ + (x i - y i)⁻
  rcases le_total (x i) (y i) with h | h
  · rw [max_eq_right h, min_eq_left h,
      posPart_of_nonpos (by linarith : x i - y i ≤ 0),
      negPart_eq_neg.mpr (by linarith : x i - y i ≤ 0)]
    ring
  · rw [max_eq_left h, min_eq_right h,
      posPart_of_nonneg (by linarith : (0:ℝ) ≤ x i - y i),
      negPart_eq_zero.mpr (by linarith : (0:ℝ) ≤ x i - y i)]
    ring

/-- **The lattice identity for quadratic forms**: the submodularity defect
is exactly the cross term between the disjointly-supported parts. -/
theorem quadForm_inf_sup {M : Matrix (Fin n) (Fin n) ℝ} (hsym : Mᵀ = M)
    (x y : Fin n → ℝ) :
    quadForm M (x ⊓ y) + quadForm M (x ⊔ y)
      = quadForm M x + quadForm M y
        + ((x - y)⁺) ⬝ᵥ (M *ᵥ ((x - y)⁻)) := by
  have e4 : quadForm M x = quadForm M (x ⊓ y + (x - y)⁺) :=
    congrArg (quadForm M) (inf_add_posPart x y).symm
  have e5 : quadForm M y = quadForm M (x ⊓ y + (x - y)⁻) :=
    congrArg (quadForm M) (inf_add_negPart x y).symm
  have e6 : quadForm M (x ⊔ y) = quadForm M (x ⊓ y + (x - y)⁺ + (x - y)⁻) :=
    congrArg (quadForm M) (sup_eq_inf_add_parts x y)
  have eA : quadForm M (x ⊓ y + (x - y)⁺ + (x - y)⁻)
      = quadForm M (x ⊓ y + (x - y)⁺) + quadForm M ((x - y)⁻)
        + (x ⊓ y + (x - y)⁺) ⬝ᵥ (M *ᵥ ((x - y)⁻)) :=
    quadForm_add hsym _ _
  have eB : quadForm M (x ⊓ y + (x - y)⁺)
      = quadForm M (x ⊓ y) + quadForm M ((x - y)⁺)
        + (x ⊓ y) ⬝ᵥ (M *ᵥ ((x - y)⁺)) :=
    quadForm_add hsym _ _
  have eC : (x ⊓ y + (x - y)⁺) ⬝ᵥ (M *ᵥ ((x - y)⁻))
      = (x ⊓ y) ⬝ᵥ (M *ᵥ ((x - y)⁻)) + ((x - y)⁺) ⬝ᵥ (M *ᵥ ((x - y)⁻)) :=
    add_dotProduct _ _ _
  have eD : quadForm M (x ⊓ y + (x - y)⁻)
      = quadForm M (x ⊓ y) + quadForm M ((x - y)⁻)
        + (x ⊓ y) ⬝ᵥ (M *ᵥ ((x - y)⁻)) :=
    quadForm_add hsym _ _
  linarith

/-- A symmetric quadratic form is submodular iff its off-diagonal entries
are nonpositive. -/
theorem submodular_quadForm_iff {M : Matrix (Fin n) (Fin n) ℝ}
    (hsym : Mᵀ = M) :
    (∀ x y : Fin n → ℝ,
        quadForm M (x ⊓ y) + quadForm M (x ⊔ y)
          ≤ quadForm M x + quadForm M y)
      ↔ ∀ i j, i ≠ j → M i j ≤ 0 := by
  constructor
  · intro h i j hij
    classical
    have hkey := h (Pi.single i 1) (Pi.single j 1)
    rw [quadForm_inf_sup hsym] at hkey
    have hpos : ((Pi.single i 1 - Pi.single j 1 : Fin n → ℝ))⁺
        = Pi.single i 1 := by
      funext k
      simp only [posPart_apply, Pi.sub_apply]
      rcases eq_or_ne k i with rfl | hki
      · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero]
        exact posPart_of_nonneg zero_le_one
      · rcases eq_or_ne k j with rfl | hkj
        · rw [Pi.single_eq_of_ne hki, Pi.single_eq_same, zero_sub]
          exact posPart_of_nonpos (by norm_num)
        · rw [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, sub_zero]
          exact posPart_of_nonpos le_rfl
    have hneg : ((Pi.single i 1 - Pi.single j 1 : Fin n → ℝ))⁻
        = Pi.single j 1 := by
      funext k
      simp only [negPart_apply, Pi.sub_apply]
      rcases eq_or_ne k i with rfl | hki
      · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero]
        exact negPart_eq_zero.mpr zero_le_one
      · rcases eq_or_ne k j with rfl | hkj
        · rw [Pi.single_eq_of_ne hki, Pi.single_eq_same, zero_sub]
          rw [negPart_eq_neg.mpr (by norm_num : (-1:ℝ) ≤ 0)]
          norm_num
        · rw [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, sub_zero]
          exact negPart_eq_zero.mpr le_rfl
    have hcross : ((Pi.single i 1 - Pi.single j 1 : Fin n → ℝ))⁺ ⬝ᵥ
        (M *ᵥ ((Pi.single i 1 - Pi.single j 1 : Fin n → ℝ))⁻) ≤ 0 := by
      linarith [hkey]
    rw [hpos, hneg] at hcross
    have hdot : (Pi.single i 1 : Fin n → ℝ) ⬝ᵥ
        (M *ᵥ (Pi.single j 1 : Fin n → ℝ)) = M i j := by
      simp [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, ite_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', mul_zero, zero_mul, mul_one,
        one_mul]
    rw [hdot] at hcross
    exact hcross
  · intro h x y
    rw [quadForm_inf_sup hsym]
    have hcross : ((x - y)⁺) ⬝ᵥ (M *ᵥ ((x - y)⁻)) ≤ 0 := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_nonpos fun i _ => ?_
      refine Finset.sum_nonpos fun j _ => ?_
      rcases eq_or_ne i j with rfl | hij
      · show (x - y)⁺ i * (M i i * (x - y)⁻ i) ≤ 0
        have heq : (x - y)⁺ i * (M i i * (x - y)⁻ i)
            = M i i * (((x - y) i)⁺ * ((x - y) i)⁻) := by
          rw [posPart_apply, negPart_apply]
          ring
        rw [heq, posPart_mul_negPart, mul_zero]
      · show (x - y)⁺ i * (M i j * (x - y)⁻ j) ≤ 0
        have h1 : (0:ℝ) ≤ (x - y)⁺ i := by
          rw [posPart_apply]
          exact posPart_nonneg _
        have h2 : (0:ℝ) ≤ (x - y)⁻ j := by
          rw [negPart_apply]
          exact negPart_nonneg _
        have h3 := h i j hij
        have h4 : M i j * ((x - y)⁺ i * (x - y)⁻ j) ≤ 0 := by
          have h5 := mul_le_mul_of_nonneg_right h3 (mul_nonneg h1 h2)
          rwa [zero_mul] at h5
        have heq : (x - y)⁺ i * (M i j * (x - y)⁻ j)
            = M i j * ((x - y)⁺ i * (x - y)⁻ j) := by ring
        rw [heq]
        exact h4
    linarith

/-! ## The conjugate of a quadratic form -/

/-- Completing the square: with `q* = Bp` and `AB = 1`,
`qᵀp - ½qᵀAq = ½pᵀBp - ½(q - q*)ᵀA(q - q*)`. -/
theorem quadForm_sq_complete {A B : Matrix (Fin n) (Fin n) ℝ}
    (hsym : Aᵀ = A) (hAB : A * B = 1) (p q : Fin n → ℝ) :
    q ⬝ᵥ p - quadForm A q = quadForm B p - quadForm A (q - B *ᵥ p) := by
  have hAqs : A *ᵥ (B *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  have e1 : quadForm A (q - B *ᵥ p)
      = quadForm A q + quadForm A (B *ᵥ p) - q ⬝ᵥ (A *ᵥ (B *ᵥ p)) :=
    quadForm_sub hsym q (B *ᵥ p)
  have e2 : quadForm A (B *ᵥ p) = quadForm B p := by
    show (B *ᵥ p) ⬝ᵥ (A *ᵥ (B *ᵥ p)) / 2 = p ⬝ᵥ (B *ᵥ p) / 2
    rw [hAqs, dotProduct_comm]
  have e3 : q ⬝ᵥ (A *ᵥ (B *ᵥ p)) = q ⬝ᵥ p := by rw [hAqs]
  rw [e1, e2, e3]
  ring

/-- The Fenchel conjugate of `½ qᵀAq` is `½ pᵀBp` for `B = A⁻¹`
(positive semidefiniteness suffices; the supremum is attained at `Bp`). -/
theorem fenchelConjugate_quadForm {A B : Matrix (Fin n) (Fin n) ℝ}
    (hsym : Aᵀ = A) (hpsd : ∀ v, 0 ≤ v ⬝ᵥ (A *ᵥ v)) (hAB : A * B = 1) :
    fenchelConjugate n (fun q => ((quadForm A q : ℝ) : EReal))
      = fun p => ((quadForm B p : ℝ) : EReal) := by
  funext p
  rw [fenchelConjugate_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun q => ?_
    rw [show ((q ⬝ᵥ p : ℝ) : EReal) - ((quadForm A q : ℝ) : EReal)
        = ((q ⬝ᵥ p - quadForm A q : ℝ) : EReal) from (EReal.coe_sub _ _).symm]
    refine EReal.coe_le_coe_iff.mpr ?_
    rw [quadForm_sq_complete hsym hAB p q]
    have h : 0 ≤ quadForm A (q - B *ᵥ p) := by
      have := hpsd (q - B *ᵥ p)
      rw [quadForm]
      linarith
    linarith
  · have hval : ((quadForm B p : ℝ) : EReal)
        = ((B *ᵥ p) ⬝ᵥ p : ℝ) - ((quadForm A (B *ᵥ p) : ℝ) : EReal) := by
      rw [show (((B *ᵥ p) ⬝ᵥ p : ℝ) : EReal) - ((quadForm A (B *ᵥ p) : ℝ) : EReal)
          = (((B *ᵥ p) ⬝ᵥ p - quadForm A (B *ᵥ p) : ℝ) : EReal)
          from (EReal.coe_sub _ _).symm]
      rw [EReal.coe_eq_coe_iff]
      have h := quadForm_sq_complete hsym hAB p (B *ᵥ p)
      rw [sub_self, quadForm_zero] at h
      linarith
    rw [hval]
    exact le_iSup (fun q => ((q ⬝ᵥ p : ℝ) : EReal) - ((quadForm A q : ℝ) : EReal))
      (B *ᵥ p)

/-! ## Convexity, lower semicontinuity, properness -/

theorem convexOn_quadForm {A : Matrix (Fin n) (Fin n) ℝ} (hsym : Aᵀ = A)
    (hpsd : ∀ v, 0 ≤ v ⬝ᵥ (A *ᵥ v)) :
    ConvexOn ℝ Set.univ (quadForm A) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hexp : quadForm A (a • x + b • y)
      = a ^ 2 * quadForm A x + b ^ 2 * quadForm A y
        + a * b * (x ⬝ᵥ (A *ᵥ y)) := by
    rw [quadForm_add hsym, quadForm_smul, quadForm_smul]
    have h : (a • x) ⬝ᵥ (A *ᵥ (b • y)) = a * b * (x ⬝ᵥ (A *ᵥ y)) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
      simp only [smul_eq_mul]
      ring
    rw [h]
  have hdiff : quadForm A (x - y)
      = quadForm A x + quadForm A y - x ⬝ᵥ (A *ᵥ y) :=
    quadForm_sub hsym x y
  have hpsd' : 0 ≤ quadForm A (x - y) := by
    have := hpsd (x - y)
    rw [quadForm]
    linarith
  have hkey : 0 ≤ a * b * quadForm A (x - y) :=
    mul_nonneg (mul_nonneg ha hb) hpsd'
  have hgoal_eq : a * quadForm A x + b * quadForm A y
      = a ^ 2 * quadForm A x + b ^ 2 * quadForm A y
        + a * b * (x ⬝ᵥ (A *ᵥ y)) + a * b * quadForm A (x - y) := by
    rw [hdiff]
    linear_combination (-(a * quadForm A x + b * quadForm A y)) * hab
  rw [hexp, hgoal_eq]
  linarith

theorem lowerSemicontinuous_coe_quadForm (A : Matrix (Fin n) (Fin n) ℝ) :
    LowerSemicontinuous fun q => ((quadForm A q : ℝ) : EReal) := by
  have hcont : Continuous (quadForm A) := by
    have h : Continuous fun q : Fin n → ℝ => q ⬝ᵥ (A *ᵥ q) := by
      simp only [dotProduct, Matrix.mulVec]
      refine continuous_finset_sum _ fun i _ => ?_
      refine (continuous_apply i).mul ?_
      exact continuous_finset_sum _ fun j _ =>
        continuous_const.mul (continuous_apply j)
    exact h.div_const 2
  exact (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/-! ## Example 2: assembly through Claim 1 -/

/-- **GHS Example 2 (roadmap item 19).** For a symmetric positive
semidefinite `A` with two-sided inverse `B`, the quadratic cost
`c(q) = ½ qᵀAq` is exchangeable iff the off-diagonal entries of `B = A⁻¹`
are nonpositive — i.e. iff `A` is an inverse Stieltjes-type matrix. -/
theorem exchangeable_quadForm_iff_offdiag_inv {A B : Matrix (Fin n) (Fin n) ℝ}
    (hsym : Aᵀ = A) (hpsd : ∀ v, 0 ≤ v ⬝ᵥ (A *ᵥ v)) (hAB : A * B = 1) :
    QOrderE (fun q => ((quadForm A q : ℝ) : EReal))
        (fun q => ((quadForm A q : ℝ) : EReal))
      ↔ ∀ i j, i ≠ j → B i j ≤ 0 := by
  have hBsym : Bᵀ = B := by
    calc Bᵀ = Bᵀ * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = (Bᵀ * Aᵀ) * B := by rw [hsym, Matrix.mul_assoc]
      _ = (A * B)ᵀ * B := by rw [Matrix.transpose_mul]
      _ = B := by rw [hAB, Matrix.transpose_one, Matrix.one_mul]
  have hconv := convexOn_quadForm hsym hpsd
  have hlsc := lowerSemicontinuous_coe_quadForm A
  have hproper := properConvexOn_coe hconv
  rw [qOrderE_iff_pOrderE_fenchelConjugate hlsc hproper hlsc hproper,
    fenchelConjugate_quadForm hsym hpsd hAB]
  rw [← submodular_quadForm_iff hBsym]
  constructor
  · intro h x y
    have hkey := h x y
    rw [show ((quadForm B (x ⊓ y) : ℝ) : EReal) + ((quadForm B (x ⊔ y) : ℝ) : EReal)
        = ((quadForm B (x ⊓ y) + quadForm B (x ⊔ y) : ℝ) : EReal)
        from (EReal.coe_add _ _).symm,
      show ((quadForm B x : ℝ) : EReal) + ((quadForm B y : ℝ) : EReal)
        = ((quadForm B x + quadForm B y : ℝ) : EReal)
        from (EReal.coe_add _ _).symm, EReal.coe_le_coe_iff] at hkey
    exact hkey
  · intro h x y
    rw [show ((quadForm B (x ⊓ y) : ℝ) : EReal) + ((quadForm B (x ⊔ y) : ℝ) : EReal)
        = ((quadForm B (x ⊓ y) + quadForm B (x ⊔ y) : ℝ) : EReal)
        from (EReal.coe_add _ _).symm,
      show ((quadForm B x : ℝ) : EReal) + ((quadForm B y : ℝ) : EReal)
        = ((quadForm B x + quadForm B y : ℝ) : EReal)
        from (EReal.coe_add _ _).symm, EReal.coe_le_coe_iff]
    exact h x y

end GHS
