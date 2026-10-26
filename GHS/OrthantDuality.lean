import GHS.Theorem3
import ConvexAnalysis.FiniteDimensional
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.LinearCombination

/-!
# GHS Phase 6, item 22: Lemma 2 (Kuhn–Tucker) via orthant duality

The waiting-time problem of GHS Appendix "Convergence of the algorithm":
`inf_{τ ≥ 0} [ q̄ᵀτ + G(α - τ) ]` with `G(β) = max_{μ ∈ D} (μᵀβ - cost μ)`
(the primal welfare, `Gfn`), against the box problem
`max_{μ ∈ D, μ ≤ q̄} (μᵀα - cost μ)` (`boxValue`).  Machine-checked:

* `weak_duality` / `boxValue_le` — every feasible pair brackets the values;
* `exists_dual_near` — **strong duality, ε-form**: for convex `D` and convex
  cost, some `τ ≥ 0` brings the waiting-time objective within `ε` of
  `boxValue`.  (The infimum need not be attained by a finite `τ` — the
  paper compactifies `τ ∈ ℝ̄₊` instead — so the ε-form is the sharp finite
  statement.)  Proof: exact-penalty value function
  `pval C y = max_{μ ∈ D} [μᵀα - cost μ - C·Σᵢ(μᵢ - q̄ᵢ - yᵢ)⁺]`, which is
  finite, concave in `y` (joint concavity + partial maximization over the
  convex `D`), and nondecreasing; a supergradient at `y = 0` is the desired
  `τ` (nonnegative by monotonicity), and `pval C 0 ↓ boxValue` as `C → ∞`
  by compactness of `D`;
* `dual_value_eq_of_slack` — **Lemma 2, sufficiency**: if Fenchel–Young is
  tight at `(μ, α - τ)` and complementary slackness `τᵀ(q̄ - μ) = 0` holds
  for a feasible pair, both problems have value `μᵀα - cost μ`;
* `kkt_of_min` — **Lemma 2, necessity**: an optimal `τ` and an optimal `μ`
  satisfy tightness and complementary slackness (the paper's
  `T^G(α,q̄) = (α - ∂G*(μ)) ∩ {τ ≥ 0} ∩ {τᵀ(q̄-μ) = 0}`, with the `γ`/`α`
  typo of the paper's statement fixed);
* `boxValue_eq_of_mem_rejectSet` — the bridge to the algorithm: a rejection
  certificate `r ∈ rejectSet p q̄` says exactly that `q̄ - r` attains
  `boxValue p q̄`.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set Filter Topology

namespace GHS

/-! ## Helpers -/

theorem posPart_mul_of_nonneg {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    (a * s)⁺ = a * s⁺ := by
  rcases le_or_gt s 0 with hs | hs
  · rw [posPart_of_nonpos hs, mul_zero,
      posPart_of_nonpos (by nlinarith : a * s ≤ 0)]
  · rw [posPart_of_nonneg hs.le, posPart_of_nonneg (by nlinarith : 0 ≤ a * s)]

theorem posPart_add_le' (a b : ℝ) : (a + b)⁺ ≤ a⁺ + b⁺ := by
  have hle : ∀ x : ℝ, x ≤ x⁺ := fun x => by
    rw [posPart_def]
    exact le_sup_left
  rw [posPart_def (a := a + b)]
  exact sup_le (add_le_add (hle a) (hle b))
    (add_nonneg (posPart_nonneg a) (posPart_nonneg b))

theorem continuous_posPart_comp {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) : Continuous fun x => (f x)⁺ := by
  have h : (fun x => (f x)⁺) = fun x => max (f x) 0 := by
    funext x
    rw [posPart_def]
  rw [h]
  exact hf.max continuous_const

/-- `exists_subgradient` transported from `Fin n → ℝ` to an arbitrary finite
index type. -/
theorem exists_subgradient_fintype {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (hf : ConvexOn ℝ Set.univ f) (x : ι → ℝ) :
    ∃ q : ι → ℝ, ∀ y, f x + q ⬝ᵥ (y - x) ≤ f y := by
  classical
  let e := Fintype.equivFin ι
  let L : (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] (ι → ℝ) := LinearMap.funLeft ℝ ℝ e
  have hF : ConvexOn ℝ Set.univ (f ∘ L) := by
    have h := hf.comp_linearMap L
    rwa [Set.preimage_univ] at h
  obtain ⟨q', hq'⟩ := exists_subgradient (f ∘ L) hF (fun j => x (e.symm j))
  refine ⟨fun i => q' (e i), fun y => ?_⟩
  have h := hq' (fun j => y (e.symm j))
  have hLx : L (fun j => x (e.symm j)) = x := by
    funext i
    simp [L, LinearMap.funLeft_apply, e.symm_apply_apply]
  have hLy : L (fun j => y (e.symm j)) = y := by
    funext i
    simp [L, LinearMap.funLeft_apply, e.symm_apply_apply]
  have hFx : (f ∘ L) (fun j => x (e.symm j)) = f x := by
    rw [Function.comp_apply, hLx]
  have hFy : (f ∘ L) (fun j => y (e.symm j)) = f y := by
    rw [Function.comp_apply, hLy]
  have hdot : q' ⬝ᵥ ((fun j => y (e.symm j)) - fun j => x (e.symm j))
      = (fun i => q' (e i)) ⬝ᵥ (y - x) := by
    simp only [dotProduct, Pi.sub_apply]
    refine Fintype.sum_equiv e.symm _ _ fun j => ?_
    simp [e.apply_symm_apply]
  rw [hFx, hFy, hdot] at h
  exact h

namespace WelfareDual

variable {ι : Type*} [Fintype ι] (W : WelfareDual ι)

/-! ## The primal welfare `G` and the two dual values -/

/-- The primal welfare function `G(β) = max_{μ ∈ D} (μᵀβ - cost μ)`. -/
noncomputable def Gfn (β : ι → ℝ) : ℝ :=
  sSup ((fun μ => μ ⬝ᵥ β - W.cost μ) '' W.D)

theorem upperSemicontinuousOn_fobj (β : ι → ℝ) :
    UpperSemicontinuousOn (fun μ => μ ⬝ᵥ β - W.cost μ) W.D := by
  have h : Continuous fun μ : ι → ℝ => μ ⬝ᵥ β := by
    simp only [dotProduct]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  have hneg : UpperSemicontinuousOn (fun μ => -W.cost μ) W.D :=
    continuous_neg.comp_lowerSemicontinuousOn_antitone W.hcost_lsc
      fun _ _ hle => neg_le_neg hle
  simpa only [sub_eq_add_neg] using h.continuousOn.upperSemicontinuousOn.add hneg

theorem exists_isMaxOn_Gfn (β : ι → ℝ) :
    ∃ μ₀ ∈ W.D, (∀ μ ∈ W.D, μ ⬝ᵥ β - W.cost μ ≤ μ₀ ⬝ᵥ β - W.cost μ₀) ∧
      W.Gfn β = μ₀ ⬝ᵥ β - W.cost μ₀ := by
  obtain ⟨μ₀, hμ₀D, hmax⟩ :=
    (W.upperSemicontinuousOn_fobj β).exists_isMaxOn
      ⟨0, W.hD_zero⟩ W.hD_compact
  refine ⟨μ₀, hμ₀D, fun μ hμ => hmax hμ, ?_⟩
  refine IsGreatest.csSup_eq ⟨⟨μ₀, hμ₀D, rfl⟩, ?_⟩
  rintro x ⟨μ, hμ, rfl⟩
  exact hmax hμ

theorem le_Gfn {β μ : ι → ℝ} (hμ : μ ∈ W.D) :
    μ ⬝ᵥ β - W.cost μ ≤ W.Gfn β := by
  obtain ⟨μ₀, hμ₀D, hmax, heq⟩ := W.exists_isMaxOn_Gfn β
  rw [heq]
  exact hmax μ hμ

/-- The box problem value `max_{μ ∈ D, μ ≤ q̄} (μᵀα - cost μ)`. -/
noncomputable def boxValue (α qb : ι → ℝ) : ℝ :=
  sSup ((fun μ => μ ⬝ᵥ α - W.cost μ) '' (W.D ∩ {μ | μ ≤ qb}))

theorem exists_isMaxOn_boxValue (α : ι → ℝ) {qb : ι → ℝ} (hqb : 0 ≤ qb) :
    ∃ μ₁ ∈ W.D ∩ {μ | μ ≤ qb},
      (∀ μ ∈ W.D ∩ {μ | μ ≤ qb}, μ ⬝ᵥ α - W.cost μ ≤ μ₁ ⬝ᵥ α - W.cost μ₁) ∧
      W.boxValue α qb = μ₁ ⬝ᵥ α - W.cost μ₁ := by
  have hcpt : IsCompact (W.D ∩ {μ | μ ≤ qb}) := by
    refine W.hD_compact.inter_right ?_
    exact isClosed_Iic (a := qb)
  have hne : (W.D ∩ {μ | μ ≤ qb}).Nonempty := ⟨0, W.hD_zero, hqb⟩
  obtain ⟨μ₁, hμ₁, hmax⟩ :=
    ((W.upperSemicontinuousOn_fobj α).mono inter_subset_left).exists_isMaxOn
      hne hcpt
  refine ⟨μ₁, hμ₁, fun μ hμ => hmax hμ, ?_⟩
  refine IsGreatest.csSup_eq ⟨⟨μ₁, hμ₁, rfl⟩, ?_⟩
  rintro x ⟨μ, hμ, rfl⟩
  exact hmax hμ

theorem le_boxValue (α : ι → ℝ) {qb μ : ι → ℝ} (hqb : 0 ≤ qb)
    (hμ : μ ∈ W.D) (hle : μ ≤ qb) :
    μ ⬝ᵥ α - W.cost μ ≤ W.boxValue α qb := by
  obtain ⟨μ₁, hμ₁, hmax, heq⟩ := W.exists_isMaxOn_boxValue α hqb
  rw [heq]
  exact hmax μ ⟨hμ, hle⟩

/-! ## Weak duality -/

theorem weak_duality (α : ι → ℝ) {qb τ μ : ι → ℝ} (hτ : 0 ≤ τ)
    (hμ : μ ∈ W.D) (hle : μ ≤ qb) :
    μ ⬝ᵥ α - W.cost μ ≤ qb ⬝ᵥ τ + W.Gfn (α - τ) := by
  have h1 : μ ⬝ᵥ (α - τ) - W.cost μ ≤ W.Gfn (α - τ) := W.le_Gfn hμ
  have h2 : μ ⬝ᵥ τ ≤ qb ⬝ᵥ τ := by
    simp only [dotProduct]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hle i) (hτ i)
  have h3 : μ ⬝ᵥ (α - τ) = μ ⬝ᵥ α - μ ⬝ᵥ τ := dotProduct_sub _ _ _
  linarith

theorem boxValue_le (α : ι → ℝ) {qb τ : ι → ℝ} (hqb : 0 ≤ qb) (hτ : 0 ≤ τ) :
    W.boxValue α qb ≤ qb ⬝ᵥ τ + W.Gfn (α - τ) := by
  obtain ⟨μ₁, ⟨hμ₁D, hμ₁le⟩, hmax, heq⟩ := W.exists_isMaxOn_boxValue α hqb
  rw [heq]
  exact W.weak_duality α hτ hμ₁D hμ₁le

/-! ## The exact-penalty value function -/

/-- The penalized objective: the box constraint `μ ≤ q̄ + y` replaced by a
linear penalty of size `C`. -/
noncomputable def pobj (α qb : ι → ℝ) (C : ℝ) (y : ι → ℝ) :
    (ι → ℝ) → ℝ :=
  fun μ => μ ⬝ᵥ α - W.cost μ - C * ∑ i, (μ i - qb i - y i)⁺

/-- The penalized value function. -/
noncomputable def pval (α qb : ι → ℝ) (C : ℝ) (y : ι → ℝ) : ℝ :=
  sSup (W.pobj α qb C y '' W.D)

theorem exists_isMaxOn_pobj (α qb : ι → ℝ) (C : ℝ) (y : ι → ℝ) :
    ∃ μ₀ ∈ W.D, (∀ μ ∈ W.D, W.pobj α qb C y μ ≤ W.pobj α qb C y μ₀) ∧
      W.pval α qb C y = W.pobj α qb C y μ₀ := by
  have hpen : Continuous fun μ : ι → ℝ =>
      -(C * ∑ i, (μ i - qb i - y i)⁺) := by
    refine continuous_neg.comp (continuous_const.mul ?_)
    exact continuous_finset_sum _ fun i _ =>
      continuous_posPart_comp
        (((continuous_apply i).sub continuous_const).sub continuous_const)
  have husc : UpperSemicontinuousOn (W.pobj α qb C y) W.D := by
    have h := (W.upperSemicontinuousOn_fobj α).add
      hpen.continuousOn.upperSemicontinuousOn
    simpa only [pobj, sub_eq_add_neg] using h
  obtain ⟨μ₀, hμ₀D, hmax⟩ :=
    husc.exists_isMaxOn ⟨0, W.hD_zero⟩ W.hD_compact
  refine ⟨μ₀, hμ₀D, fun μ hμ => hmax hμ, ?_⟩
  refine IsGreatest.csSup_eq ⟨⟨μ₀, hμ₀D, rfl⟩, ?_⟩
  rintro x ⟨μ, hμ, rfl⟩
  exact hmax hμ

theorem le_pval (α qb : ι → ℝ) (C : ℝ) (y : ι → ℝ) {μ : ι → ℝ}
    (hμ : μ ∈ W.D) : W.pobj α qb C y μ ≤ W.pval α qb C y := by
  obtain ⟨μ₀, hμ₀D, hmax, heq⟩ := W.exists_isMaxOn_pobj α qb C y
  rw [heq]
  exact hmax μ hμ

theorem pval_mono (α qb : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) {y y' : ι → ℝ}
    (h : y ≤ y') : W.pval α qb C y ≤ W.pval α qb C y' := by
  obtain ⟨μ₀, hμ₀D, hmax, heq⟩ := W.exists_isMaxOn_pobj α qb C y
  rw [heq]
  refine le_trans ?_ (W.le_pval α qb C y' hμ₀D)
  unfold pobj
  have hpen : ∑ i, (μ₀ i - qb i - y' i)⁺ ≤ ∑ i, (μ₀ i - qb i - y i)⁺ := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine posPart_mono ?_
    have := h i
    linarith
  have := mul_le_mul_of_nonneg_left hpen hC
  linarith

/-- The penalized value is concave in the perturbation `y` (as convexity of
its negative): partial maximization over the convex `D` of a jointly concave
function. -/
theorem convexOn_neg_pval (α qb : ι → ℝ) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) {C : ℝ} (hC : 0 ≤ C) :
    ConvexOn ℝ Set.univ fun y => -(W.pval α qb C y) := by
  refine ⟨convex_univ, ?_⟩
  intro y₁ _ y₂ _ a b ha hb hab
  simp only [smul_eq_mul]
  obtain ⟨μ₁, hμ₁D, -, heq₁⟩ := W.exists_isMaxOn_pobj α qb C y₁
  obtain ⟨μ₂, hμ₂D, -, heq₂⟩ := W.exists_isMaxOn_pobj α qb C y₂
  have hμaD : a • μ₁ + b • μ₂ ∈ W.D := hDconv hμ₁D hμ₂D ha hb hab
  have hcost : W.cost (a • μ₁ + b • μ₂) ≤ a * W.cost μ₁ + b * W.cost μ₂ := by
    have h := hcost_conv.2 hμ₁D hμ₂D ha hb hab
    simpa [smul_eq_mul] using h
  have hlin : (a • μ₁ + b • μ₂) ⬝ᵥ α = a * (μ₁ ⬝ᵥ α) + b * (μ₂ ⬝ᵥ α) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
  have hpen : ∑ i, ((a • μ₁ + b • μ₂) i - qb i - (a • y₁ + b • y₂) i)⁺
      ≤ a * (∑ i, (μ₁ i - qb i - y₁ i)⁺)
        + b * (∑ i, (μ₂ i - qb i - y₂ i)⁺) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have harg : (a • μ₁ + b • μ₂) i - qb i - (a • y₁ + b • y₂) i
        = a * (μ₁ i - qb i - y₁ i) + b * (μ₂ i - qb i - y₂ i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination qb i * hab
    rw [harg]
    calc (a * (μ₁ i - qb i - y₁ i) + b * (μ₂ i - qb i - y₂ i))⁺
        ≤ (a * (μ₁ i - qb i - y₁ i))⁺ + (b * (μ₂ i - qb i - y₂ i))⁺ :=
          posPart_add_le' _ _
      _ = a * (μ₁ i - qb i - y₁ i)⁺ + b * (μ₂ i - qb i - y₂ i)⁺ := by
          rw [posPart_mul_of_nonneg ha, posPart_mul_of_nonneg hb]
  have hval : W.pobj α qb C (a • y₁ + b • y₂) (a • μ₁ + b • μ₂)
      ≤ W.pval α qb C (a • y₁ + b • y₂) :=
    W.le_pval α qb C _ hμaD
  have hpen' : C * (∑ i, ((a • μ₁ + b • μ₂) i - qb i - (a • y₁ + b • y₂) i)⁺)
      ≤ C * (a * (∑ i, (μ₁ i - qb i - y₁ i)⁺)
        + b * (∑ i, (μ₂ i - qb i - y₂ i)⁺)) :=
    mul_le_mul_of_nonneg_left hpen hC
  rw [heq₁, heq₂]
  unfold pobj at hval ⊢
  nlinarith [hval, hcost, hlin, hpen']

/-! ## Exactness of the penalty as `C → ∞` -/

theorem exists_pval_le (α : ι → ℝ) {qb : ι → ℝ} (hqb : 0 ≤ qb) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ m : ℕ, W.pval α qb (m : ℝ) 0 ≤ W.boxValue α qb + ε := by
  by_contra hcon
  push_neg at hcon
  have hch : ∀ m : ℕ, ∃ μm ∈ W.D,
      (∀ μ ∈ W.D, W.pobj α qb (m : ℝ) 0 μ ≤ W.pobj α qb (m : ℝ) 0 μm) ∧
      W.pval α qb (m : ℝ) 0 = W.pobj α qb (m : ℝ) 0 μm :=
    fun m => W.exists_isMaxOn_pobj α qb (m : ℝ) 0
  choose μs hμsD hmax hval using hch
  -- notation: the unpenalized objective and the penalty
  set f : (ι → ℝ) → ℝ := fun μ => μ ⬝ᵥ α - W.cost μ with hf_def
  set pen : (ι → ℝ) → ℝ := fun μ => ∑ i, (μ i - qb i)⁺ with hpen_def
  have hpobj0 : ∀ (C : ℝ) (μ : ι → ℝ),
      W.pobj α qb C 0 μ = f μ - C * pen μ := by
    intro C μ
    simp only [pobj, hf_def, hpen_def, Pi.zero_apply, sub_zero]
  have hpen_nonneg : ∀ μ, 0 ≤ pen μ := fun μ =>
    Finset.sum_nonneg fun i _ => posPart_nonneg _
  have hfG : ∀ μ ∈ W.D, f μ ≤ W.Gfn α := fun μ hμ => W.le_Gfn hμ
  -- the uniform bound on m · pen (μs m)
  set B : ℝ := W.Gfn α - W.boxValue α qb - ε with hB_def
  have hkey : ∀ m : ℕ, (m : ℝ) * pen (μs m) < B := by
    intro m
    have h1 := hcon m
    rw [hval m, hpobj0] at h1
    have h2 := hfG (μs m) (hμsD m)
    rw [hB_def]
    linarith
  have hBpos : 0 < B := by
    have h := hkey 0
    rwa [Nat.cast_zero, zero_mul] at h
  -- the compactness extraction
  obtain ⟨μhat, hμhatD, φ, hφ, htend⟩ := W.hD_compact.tendsto_subseq hμsD
  have hpencont : Continuous pen := by
    rw [hpen_def]
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_posPart_comp ((continuous_apply i).sub continuous_const)
  have htendpen : Tendsto (fun k => pen (μs (φ k))) atTop (𝓝 (pen μhat)) :=
    (hpencont.tendsto μhat).comp htend
  -- pen μhat = 0, so μhat is feasible
  have hple : pen μhat ≤ 0 := by
    have htendB : Tendsto (fun k : ℕ => B / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat B
    refine le_of_tendsto_of_tendsto htendpen htendB ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hφk : (1:ℕ) ≤ φ k := le_trans hk hφ.le_apply
    have hφkpos : (0:ℝ) < (φ k : ℝ) := by exact_mod_cast hφk
    have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h1 : pen (μs (φ k)) < B / (φ k : ℝ) := by
      rw [lt_div_iff₀ hφkpos]
      have h := hkey (φ k)
      linarith
    have h2 : B / (φ k : ℝ) ≤ B / (k : ℝ) := by
      have hone : 1 / (φ k : ℝ) ≤ 1 / (k : ℝ) := by
        refine one_div_le_one_div_of_le hkpos ?_
        exact_mod_cast hφ.le_apply
      calc B / (φ k : ℝ) = B * (1 / (φ k : ℝ)) := by ring
        _ ≤ B * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_left hone hBpos.le
        _ = B / (k : ℝ) := by ring
    linarith
  have hpen0 : pen μhat = 0 := le_antisymm hple (hpen_nonneg μhat)
  have hμhatle : μhat ≤ qb := by
    intro i
    rw [hpen_def] at hpen0
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => posPart_nonneg (μhat j - qb j))).mp hpen0 i (Finset.mem_univ i)
    have h2 : μhat i - qb i ≤ 0 := posPart_eq_zero.mp h
    show μhat i ≤ qb i
    linarith
  have hfeas : f μhat ≤ W.boxValue α qb := W.le_boxValue α hqb hμhatD hμhatle
  -- but the limit of the values stays above boxValue + ε
  have hflarge : ∀ m : ℕ, W.boxValue α qb + ε ≤ f (μs m) := by
    intro m
    have h1 := hcon m
    rw [hval m, hpobj0] at h1
    have h2 : 0 ≤ (m : ℝ) * pen (μs m) :=
      mul_nonneg (Nat.cast_nonneg m) (hpen_nonneg (μs m))
    linarith
  have hfhat : W.boxValue α qb + ε ≤ f μhat := by
    have hcpt := (W.upperSemicontinuousOn_fobj α).isCompact_inter_preimage_Ici
      W.hD_compact (W.boxValue α qb + ε)
    have hmem : ∀ k, μs (φ k) ∈
        W.D ∩ f ⁻¹' Ici (W.boxValue α qb + ε) :=
      fun k => ⟨hμsD (φ k), hflarge (φ k)⟩
    exact (hcpt.isClosed.mem_of_tendsto htend (Eventually.of_forall hmem)).2
  linarith

/-! ## Strong duality (ε-form) -/

/-- **Strong orthant duality, ε-form.** For convex welfare data, some
`τ ≥ 0` brings the waiting-time objective within `ε` of the box value. -/
theorem exists_dual_near (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ) {qb : ι → ℝ}
    (hqb : 0 ≤ qb) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ, 0 ≤ τ ∧ qb ⬝ᵥ τ + W.Gfn (α - τ) ≤ W.boxValue α qb + ε := by
  classical
  obtain ⟨m, hm⟩ := W.exists_pval_le α hqb hε
  set C : ℝ := (m : ℝ) with hC_def
  have hC : 0 ≤ C := Nat.cast_nonneg m
  have hconv := W.convexOn_neg_pval α qb hDconv hcost_conv hC
  obtain ⟨q, hq⟩ := exists_subgradient_fintype _ hconv 0
  set τ : ι → ℝ := -q with hτ_def
  -- the supergradient inequality: pval C y ≤ pval C 0 + τ ⬝ᵥ y
  have hsg : ∀ y, W.pval α qb C y ≤ W.pval α qb C 0 + τ ⬝ᵥ y := by
    intro y
    have h : -(W.pval α qb C 0) + q ⬝ᵥ (y - 0) ≤ -(W.pval α qb C y) := hq y
    rw [sub_zero] at h
    have h2 : τ ⬝ᵥ y = -(q ⬝ᵥ y) := by
      rw [hτ_def, neg_dotProduct]
    linarith
  -- nonnegativity of τ from monotonicity of pval
  have hτ0 : 0 ≤ τ := by
    intro i
    have hy : (0 : ι → ℝ) ≤ (Pi.single i 1 : ι → ℝ) := by
      intro j
      show (0:ℝ) ≤ (Pi.single i 1 : ι → ℝ) j
      rw [Pi.single_apply]
      split <;> norm_num
    have h1 : W.pval α qb C 0 ≤ W.pval α qb C (Pi.single i 1) :=
      W.pval_mono α qb hC hy
    have h2 := hsg (Pi.single i 1)
    have h3 : τ ⬝ᵥ (Pi.single i 1 : ι → ℝ) = τ i := by
      simp [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq']
    show (0:ℝ) ≤ τ i
    linarith
  refine ⟨τ, hτ0, ?_⟩
  -- evaluate `G` at `α - τ`, and perturb by `y₀ = μ₀ - q̄`
  obtain ⟨μ₀, hμ₀D, hmax₀, heq₀⟩ := W.exists_isMaxOn_Gfn (α - τ)
  have hy₀ : W.pobj α qb C (μ₀ - qb) μ₀ = μ₀ ⬝ᵥ α - W.cost μ₀ := by
    unfold pobj
    have hz : ∀ i, (μ₀ i - qb i - (μ₀ - qb) i)⁺ = 0 := by
      intro i
      have h : μ₀ i - qb i - (μ₀ - qb) i = 0 := by
        show μ₀ i - qb i - (μ₀ i - qb i) = 0
        ring
      rw [h]
      exact posPart_of_nonpos le_rfl
    rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_const_zero, mul_zero,
      sub_zero]
  have h1 : μ₀ ⬝ᵥ α - W.cost μ₀ ≤ W.pval α qb C (μ₀ - qb) := by
    rw [← hy₀]
    exact W.le_pval α qb C _ hμ₀D
  have h2 := hsg (μ₀ - qb)
  rw [heq₀, dotProduct_sub]
  have h3 : qb ⬝ᵥ τ = τ ⬝ᵥ qb := dotProduct_comm _ _
  have h4 : μ₀ ⬝ᵥ τ = τ ⬝ᵥ μ₀ := dotProduct_comm _ _
  have h5 : τ ⬝ᵥ (μ₀ - qb) = τ ⬝ᵥ μ₀ - τ ⬝ᵥ qb := dotProduct_sub _ _ _
  linarith

/-! ## Lemma 2 (Kuhn–Tucker) -/

/-- **Lemma 2, sufficiency**: a feasible pair `(τ, μ)` with tight
Fenchel–Young (`α - τ ∈ ∂G*(μ)`) and complementary slackness has both the
waiting-time and the box objectives equal to `μᵀα - cost μ`. -/
theorem dual_value_eq_of_slack (α : ι → ℝ) {qb τ μ : ι → ℝ} (hqb : 0 ≤ qb)
    (hτ : 0 ≤ τ) (hμD : μ ∈ W.D) (hle : μ ≤ qb)
    (htight : W.Gfn (α - τ) = μ ⬝ᵥ (α - τ) - W.cost μ)
    (hslack : τ ⬝ᵥ (qb - μ) = 0) :
    qb ⬝ᵥ τ + W.Gfn (α - τ) = W.boxValue α qb := by
  have hval : qb ⬝ᵥ τ + W.Gfn (α - τ) = μ ⬝ᵥ α - W.cost μ := by
    rw [htight, dotProduct_sub]
    have h1 : τ ⬝ᵥ (qb - μ) = τ ⬝ᵥ qb - τ ⬝ᵥ μ := dotProduct_sub _ _ _
    have h2 : qb ⬝ᵥ τ = τ ⬝ᵥ qb := dotProduct_comm _ _
    have h3 : μ ⬝ᵥ τ = τ ⬝ᵥ μ := dotProduct_comm _ _
    linarith [hslack]
  rw [hval]
  refine le_antisymm (W.le_boxValue α hqb hμD hle) ?_
  rw [← hval]
  exact W.boxValue_le α hqb hτ

/-- **Lemma 2, sufficiency, minimality form**: under tightness and
complementary slackness, `τ` minimizes the waiting-time objective over the
nonnegative orthant. -/
theorem isMin_of_slack (α : ι → ℝ) {qb τ μ : ι → ℝ} (hqb : 0 ≤ qb)
    (hτ : 0 ≤ τ) (hμD : μ ∈ W.D) (hle : μ ≤ qb)
    (htight : W.Gfn (α - τ) = μ ⬝ᵥ (α - τ) - W.cost μ)
    (hslack : τ ⬝ᵥ (qb - μ) = 0) {τ' : ι → ℝ} (hτ' : 0 ≤ τ') :
    qb ⬝ᵥ τ + W.Gfn (α - τ) ≤ qb ⬝ᵥ τ' + W.Gfn (α - τ') := by
  rw [W.dual_value_eq_of_slack α hqb hτ hμD hle htight hslack]
  exact W.boxValue_le α hqb hτ'

/-- **Lemma 2, necessity (GHS lem:kuhnTucker, `γ`/`α` typo fixed)**: if
`τ ≥ 0` minimizes the waiting-time objective and `μ` attains the box value,
then Fenchel–Young is tight at `(μ, α - τ)` — the paper's
`τ ∈ α - ∂G*(μ)` — and complementary slackness `τᵀ(q̄ - μ) = 0` holds. -/
theorem kkt_of_min (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ) {qb τ μ : ι → ℝ}
    (hqb : 0 ≤ qb) (hτ : 0 ≤ τ)
    (hmin : ∀ τ', 0 ≤ τ' →
      qb ⬝ᵥ τ + W.Gfn (α - τ) ≤ qb ⬝ᵥ τ' + W.Gfn (α - τ'))
    (hμD : μ ∈ W.D) (hle : μ ≤ qb)
    (hopt : W.boxValue α qb = μ ⬝ᵥ α - W.cost μ) :
    W.Gfn (α - τ) = μ ⬝ᵥ (α - τ) - W.cost μ ∧ τ ⬝ᵥ (qb - μ) = 0 := by
  have hub : qb ⬝ᵥ τ + W.Gfn (α - τ) ≤ μ ⬝ᵥ α - W.cost μ := by
    rw [← hopt]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨τ', hτ', hτ'val⟩ := W.exists_dual_near hDconv hcost_conv α hqb hε
    exact le_trans (hmin τ' hτ') hτ'val
  have hFY : μ ⬝ᵥ (α - τ) - W.cost μ ≤ W.Gfn (α - τ) := W.le_Gfn hμD
  have hsl : 0 ≤ τ ⬝ᵥ (qb - μ) := by
    simp only [dotProduct, Pi.sub_apply]
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 : (0:ℝ) ≤ τ i := hτ i
    have h2 : μ i ≤ qb i := hle i
    nlinarith
  have h1 : τ ⬝ᵥ (qb - μ) = τ ⬝ᵥ qb - τ ⬝ᵥ μ := dotProduct_sub _ _ _
  have h2 : μ ⬝ᵥ (α - τ) = μ ⬝ᵥ α - μ ⬝ᵥ τ := dotProduct_sub _ _ _
  have h3 : qb ⬝ᵥ τ = τ ⬝ᵥ qb := dotProduct_comm _ _
  have h4 : μ ⬝ᵥ τ = τ ⬝ᵥ μ := dotProduct_comm _ _
  constructor
  · refine le_antisymm ?_ hFY
    linarith
  · linarith

/-! ## Bridge to the algorithm's rejection certificates -/

/-- A rejection certificate identifies the box value: if
`r ∈ rejectSet p q̄` then the accepted mass `q̄ - r` attains
`boxValue p q̄`. -/
theorem boxValue_eq_of_mem_rejectSet {p qb r : ι → ℝ} (hqb : 0 ≤ qb)
    (hr : r ∈ W.rejectSet p qb) :
    W.boxValue p qb = (qb - r) ⬝ᵥ p - W.cost (qb - r) := by
  obtain ⟨hr0, hrD, hopt⟩ := (W.mem_rejectSet_iff_acceptance hqb).mp hr
  have hrle : qb - r ≤ qb := by
    intro i
    have h : (0:ℝ) ≤ r i := hr0 i
    show qb i - r i ≤ qb i
    linarith
  refine le_antisymm ?_ (W.le_boxValue p hqb hrD hrle)
  obtain ⟨μ₁, ⟨hμ₁D, hμ₁le⟩, hmax, heq⟩ := W.exists_isMaxOn_boxValue p hqb
  rw [heq]
  have h := hopt μ₁ hμ₁D hμ₁le
  simp only [aobj] at h
  have hc1 : μ₁ ⬝ᵥ p = p ⬝ᵥ μ₁ := dotProduct_comm _ _
  have hc2 : (qb - r) ⬝ᵥ p = p ⬝ᵥ (qb - r) := dotProduct_comm _ _
  linarith

/-! ## The G4 step of Lemma 3: tightening the capacity to the acceptance -/

theorem boxValue_mono (α : ι → ℝ) {qb qb' : ι → ℝ} (hqb' : 0 ≤ qb')
    (h : qb' ≤ qb) : W.boxValue α qb' ≤ W.boxValue α qb := by
  have hqb : 0 ≤ qb := le_trans hqb' h
  obtain ⟨μ₁, ⟨hμ₁D, hμ₁le⟩, hmax, heq⟩ := W.exists_isMaxOn_boxValue α hqb'
  rw [heq]
  exact W.le_boxValue α hqb hμ₁D (le_trans hμ₁le h)

/-- **The unjustified step of the paper's Lemma 3 (erratum G4), repaired at
the level of values:** tightening the capacity from `q̄` to an optimal
accepted mass `μT` does not change the box value — hence, by strong
duality, neither the value of the waiting-time problem
(`inf T^H(γ, μ^P) = inf T^H(γ, μ^T)` in the paper's notation). -/
theorem boxValue_capacity_eq_of_opt (α : ι → ℝ) {qb μT : ι → ℝ}
    (hqb : 0 ≤ qb) (hμT0 : 0 ≤ μT) (hμTD : μT ∈ W.D) (hle : μT ≤ qb)
    (hopt : W.boxValue α qb = μT ⬝ᵥ α - W.cost μT) :
    W.boxValue α μT = W.boxValue α qb := by
  refine le_antisymm (W.boxValue_mono α hμT0 hle) ?_
  rw [hopt]
  exact W.le_boxValue α hμT0 hμTD (le_refl μT)

/-- The G4 repair in the algorithm's vocabulary: after the disposal phase
at capacity `q̄` with rejection `r`, re-running it at the tightened capacity
`q̄ - r` (the tentative acceptance) leaves the box value unchanged. -/
theorem boxValue_capacity_eq_of_mem_rejectSet {p qb r : ι → ℝ}
    (hqb : 0 ≤ qb) (hDpos : ∀ μ ∈ W.D, 0 ≤ μ)
    (hr : r ∈ W.rejectSet p qb) :
    W.boxValue p (qb - r) = W.boxValue p qb := by
  obtain ⟨hr0, hrD, -⟩ := (W.mem_rejectSet_iff_acceptance hqb).mp hr
  refine W.boxValue_capacity_eq_of_opt p hqb (hDpos _ hrD) hrD ?_ ?_
  · intro i
    have h : (0:ℝ) ≤ r i := hr0 i
    show qb i - r i ≤ qb i
    linarith
  · exact W.boxValue_eq_of_mem_rejectSet hqb hr

end WelfareDual

end GHS
