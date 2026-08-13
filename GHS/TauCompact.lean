import GHS.OrthantDuality
import GHS.Conjugacy
import GHS.DeferredAcceptance
import GHS.Proposition3
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Compactified waiting times

This file implements the paper's waiting-time compactification using
`τ : ι → ℝ≥0∞`.  The nonnegative pairing is computed in `ENNReal`, whose
multiplication has the required convention `0 * ∞ = 0`, and is embedded only
once into `EReal`.

For `μ ≥ 0`, the extended welfare payoff at `α - τ` is represented without an
indeterminate `∞ - ∞` as

`μᵀ α - cost μ - Σ i, μ i * τ i`.

The extended welfare is the supremum of these payoffs over `D`.  Since `0 ∈ D`,
it is never `⊥`; consequently the compactified objective
`qbᵀ τ + Gext(α,τ)` is unambiguous even when some waiting times are infinite.
On finite nonnegative waiting times it is exactly the real objective from
`OrthantDuality.lean`.

## Hypothesis audit for the paper's final normalization

Exact attainment, KKT, Lemma 3, closed-graph passage to the monotone waiting-time
limits, and the final normalized equilibrium are proved below.  The paper's
coordinatewise normalization
`min (τα i) (τγ i) = 0` genuinely uses side-specific capacity bounds
`D_G ≤ nG`, `D_H ≤ nH` and the initialization `A0 = nG ⊓ nH`.  Those data
are not fields of `WelfareDual`, whose algorithm API permits arbitrary
nonnegative `A0`; they must be added explicitly to the corrected final
statement.  Receiver monotonicity also needs the symmetric hypothesis
`Exchangeable WH.cFn`.
-/

open Set Filter Topology

namespace GHS
namespace WelfareDual

variable {ι : Type*} [Fintype ι] (W : WelfareDual ι)

/-- A finite nonnegative real vector embedded in compactified waiting-time space. -/
noncomputable def tauOfReal (τ : ι → ℝ) : ι → ENNReal :=
  fun i => ENNReal.ofReal (τ i)

/-- The compactified nonnegative pairing.  In particular, a zero coefficient
contributes zero even at an infinite waiting time. -/
noncomputable def tauPair (a : ι → ℝ) (τ : ι → ENNReal) : ENNReal :=
  ∑ i, ENNReal.ofReal (a i) * τ i

/-- A dual-domain point's extended affine payoff at `α - τ`. -/
noncomputable def extPayoff (α μ : ι → ℝ) (τ : ι → ENNReal) : EReal :=
  ((μ ⬝ᵥ α - W.cost μ : ℝ) : EReal) - (tauPair μ τ : EReal)

/-- `G(α - τ)` on compactified waiting times, defined by the paper's supremum
formula and the convention `0 * ∞ = 0`. -/
noncomputable def Gext (α : ι → ℝ) (τ : ι → ENNReal) : EReal :=
  ⨆ μ : W.D, W.extPayoff α μ τ

/-- The compactified waiting-time objective. -/
noncomputable def tauObjective (α qb : ι → ℝ) (τ : ι → ENNReal) : EReal :=
  (tauPair qb τ : EReal) + W.Gext α τ

theorem continuous_tauPair (a : ι → ℝ) : Continuous (tauPair a) := by
  unfold tauPair
  exact continuous_finset_sum _ fun i _ =>
    ENNReal.continuous_const_mul ENNReal.ofReal_ne_top |>.comp
      (continuous_apply i)

theorem continuous_extPayoff (α μ : ι → ℝ) : Continuous (W.extPayoff α μ) := by
  have hp : Continuous fun τ : ι → ENNReal => (tauPair μ τ : EReal) :=
    continuous_coe_ennreal_ereal.comp (continuous_tauPair μ)
  rw [continuous_iff_continuousAt]
  intro τ
  unfold extPayoff
  exact (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _))
    (Or.inl (EReal.coe_ne_bot _))).comp
      (continuousAt_const.prodMk (hp.neg.continuousAt))

theorem lowerSemicontinuous_Gext (α : ι → ℝ) :
    LowerSemicontinuous (W.Gext α) := by
  unfold Gext
  exact lowerSemicontinuous_iSup fun μ => (W.continuous_extPayoff α μ).lowerSemicontinuous

theorem Gext_ne_bot (α : ι → ℝ) (τ : ι → ENNReal) : W.Gext α τ ≠ ⊥ := by
  have hzero : W.extPayoff α 0 τ = ((-W.cost 0 : ℝ) : EReal) := by
    unfold extPayoff tauPair
    simp
  have hle : W.extPayoff α (⟨0, W.hD_zero⟩ : W.D) τ ≤ W.Gext α τ :=
    le_iSup (fun μ : W.D => W.extPayoff α μ τ) ⟨0, W.hD_zero⟩
  rw [hzero] at hle
  exact ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) hle)

theorem lowerSemicontinuous_tauObjective (α qb : ι → ℝ) :
    LowerSemicontinuous (W.tauObjective α qb) := by
  unfold tauObjective
  have hp : LowerSemicontinuous fun τ : ι → ENNReal => (tauPair qb τ : EReal) :=
    (continuous_coe_ennreal_ereal.comp (continuous_tauPair qb)).lowerSemicontinuous
  refine hp.add' (W.lowerSemicontinuous_Gext α) fun τ => ?_
  exact EReal.continuousAt_add (Or.inr (W.Gext_ne_bot α τ))
    (Or.inl (by simp : (tauPair qb τ : EReal) ≠ ⊥))

theorem tauPair_tauOfReal {a τ : ι → ℝ} (ha : 0 ≤ a) (hτ : 0 ≤ τ) :
    tauPair a (tauOfReal τ) = ENNReal.ofReal (a ⬝ᵥ τ) := by
  unfold tauPair tauOfReal dotProduct
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.ofReal_mul (ha i)]
  · intro i hi
    exact mul_nonneg (ha i) (hτ i)

theorem tauPair_mono_right {a : ι → ℝ} (ha : 0 ≤ a)
    {τ σ : ι → ENNReal} (hτσ : τ ≤ σ) : tauPair a τ ≤ tauPair a σ := by
  unfold tauPair
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_left' (hτσ i) _

theorem extPayoff_tauOfReal {α μ τ : ι → ℝ} (hμ : 0 ≤ μ) (hτ : 0 ≤ τ) :
    W.extPayoff α μ (tauOfReal τ) =
      ((μ ⬝ᵥ (α - τ) - W.cost μ : ℝ) : EReal) := by
  unfold extPayoff
  have hdot : 0 ≤ μ ⬝ᵥ τ := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (hτ i)
  rw [tauPair_tauOfReal hμ hτ, EReal.coe_ennreal_ofReal,
    max_eq_left hdot, ← EReal.coe_sub]
  congr 1
  rw [dotProduct_sub]
  ring

theorem Gext_tauOfReal (hDpos : ∀ μ ∈ W.D, 0 ≤ μ) (α : ι → ℝ)
    {τ : ι → ℝ} (hτ : 0 ≤ τ) :
    W.Gext α (tauOfReal τ) = ((W.Gfn (α - τ) : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun μ => ?_
    rw [W.extPayoff_tauOfReal (hDpos μ μ.property) hτ]
    exact EReal.coe_le_coe_iff.mpr (W.le_Gfn μ.property)
  · obtain ⟨μ, hμD, hmax, heq⟩ := W.exists_isMaxOn_Gfn (α - τ)
    rw [heq]
    have hle := le_iSup (fun ν : W.D => W.extPayoff α ν (tauOfReal τ))
      (⟨μ, hμD⟩ : W.D)
    rw [W.extPayoff_tauOfReal (hDpos μ hμD) hτ] at hle
    exact hle

/-- The compactified objective agrees exactly with the old finite objective. -/
theorem tauObjective_tauOfReal (hDpos : ∀ μ ∈ W.D, 0 ≤ μ)
    {α qb τ : ι → ℝ} (hqb : 0 ≤ qb) (hτ : 0 ≤ τ) :
    W.tauObjective α qb (tauOfReal τ) =
      ((qb ⬝ᵥ τ + W.Gfn (α - τ) : ℝ) : EReal) := by
  unfold tauObjective
  have hdot : 0 ≤ qb ⬝ᵥ τ := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hqb i) (hτ i)
  rw [tauPair_tauOfReal hqb hτ, EReal.coe_ennreal_ofReal,
    max_eq_left hdot, W.Gext_tauOfReal hDpos α hτ,
    ← EReal.coe_add]

/-! ## Attainment and exact strong duality -/

/-- The compactified waiting-time objective attains its minimum. -/
theorem exists_isMin_tauObjective (α qb : ι → ℝ) :
    ∃ τ : ι → ENNReal, ∀ τ', W.tauObjective α qb τ ≤ W.tauObjective α qb τ' := by
  have hlscOn : LowerSemicontinuousOn (W.tauObjective α qb) Set.univ :=
    (W.lowerSemicontinuous_tauObjective α qb).lowerSemicontinuousOn Set.univ
  obtain ⟨τ, -, hτ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (univ_nonempty : (Set.univ : Set (ι → ENNReal)).Nonempty) isCompact_univ hlscOn
  exact ⟨τ, fun τ' => hτ (mem_univ τ')⟩

/-- Compactified weak duality. -/
theorem boxValue_le_tauObjective (hDpos : ∀ μ ∈ W.D, 0 ≤ μ)
    (α : ι → ℝ) {qb : ι → ℝ} (hqb : 0 ≤ qb) (τ : ι → ENNReal) :
    ((W.boxValue α qb : ℝ) : EReal) ≤ W.tauObjective α qb τ := by
  obtain ⟨μ, ⟨hμD, hμle⟩, hmax, hopt⟩ := W.exists_isMaxOn_boxValue α hqb
  have hμ0 := hDpos μ hμD
  have hpair : tauPair μ τ ≤ tauPair qb τ := by
    unfold tauPair
    refine Finset.sum_le_sum fun i _ => ?_
    gcongr
    exact hμle i
  by_cases hqtop : tauPair qb τ = ⊤
  · unfold tauObjective
    have htopE : (tauPair qb τ : EReal) = ⊤ := by rw [hqtop]; rfl
    rw [htopE]
    rw [EReal.top_add_of_ne_bot (W.Gext_ne_bot α τ)]
    exact le_top
  have hμtop : tauPair μ τ ≠ ⊤ := ne_top_of_le_ne_top hqtop hpair
  have hpay : W.extPayoff α (⟨μ, hμD⟩ : W.D) τ ≤ W.Gext α τ :=
    le_iSup (fun ν : W.D => W.extPayoff α ν τ) ⟨μ, hμD⟩
  have hrealPair : (tauPair μ τ).toReal ≤ (tauPair qb τ).toReal :=
    ENNReal.toReal_mono hqtop hpair
  rw [hopt]
  calc
    ((μ ⬝ᵥ α - W.cost μ : ℝ) : EReal) ≤
        (tauPair qb τ : EReal) + W.extPayoff α (⟨μ, hμD⟩ : W.D) τ := by
      unfold extPayoff
      rw [← EReal.coe_ennreal_toReal hqtop, ← EReal.coe_ennreal_toReal hμtop,
        ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith
    _ ≤ (tauPair qb τ : EReal) + W.Gext α τ := add_le_add le_rfl hpay
    _ = W.tauObjective α qb τ := rfl

/-- **Exact compactified strong duality.** The attained minimum of the
compactified waiting-time problem equals the box value. -/
theorem exists_tauObjective_eq_boxValue
    (hDpos : ∀ μ ∈ W.D, 0 ≤ μ) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ)
    {qb : ι → ℝ} (hqb : 0 ≤ qb) :
    ∃ τ : ι → ENNReal,
      W.tauObjective α qb τ = ((W.boxValue α qb : ℝ) : EReal) ∧
      ∀ τ', W.tauObjective α qb τ ≤ W.tauObjective α qb τ' := by
  obtain ⟨τ, hmin⟩ := W.exists_isMin_tauObjective α qb
  have hlower := W.boxValue_le_tauObjective hDpos α hqb τ
  have hub (ε : ℝ) (hε : 0 < ε) :
      W.tauObjective α qb τ ≤ ((W.boxValue α qb + ε : ℝ) : EReal) := by
    obtain ⟨t, ht0, ht⟩ := W.exists_dual_near hDconv hcost_conv α hqb hε
    calc
      W.tauObjective α qb τ ≤ W.tauObjective α qb (tauOfReal t) := hmin _
      _ = ((qb ⬝ᵥ t + W.Gfn (α - t) : ℝ) : EReal) :=
        W.tauObjective_tauOfReal hDpos hqb ht0
      _ ≤ ((W.boxValue α qb + ε : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr ht
  have htop : W.tauObjective α qb τ ≠ ⊤ := by
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (hub 1 one_pos)
  have hbot : W.tauObjective α qb τ ≠ ⊥ := by
    exact ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) hlower)
  lift W.tauObjective α qb τ to ℝ using ⟨htop, hbot⟩ with r hr
  have hrle : r ≤ W.boxValue α qb := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := hub ε hε
    exact EReal.coe_le_coe_iff.mp h
  have heq : W.tauObjective α qb τ = ((W.boxValue α qb : ℝ) : EReal) := by
    apply le_antisymm
    · rw [← hr]
      exact EReal.coe_le_coe_iff.mpr hrle
    · rw [← hr]
      exact hlower
  refine ⟨τ, heq, fun τ' => ?_⟩
  rw [← hr]
  exact hmin τ'

/-! ## Exact compactified KKT -/

/-- The attained compactified waiting-time set `T^G(α,qb)`. -/
noncomputable def tauMinSet (α qb : ι → ℝ) : Set (ι → ENNReal) :=
  {τ | ∀ τ', W.tauObjective α qb τ ≤ W.tauObjective α qb τ'}

theorem tauMinSet_nonempty (α qb : ι → ℝ) : (W.tauMinSet α qb).Nonempty := by
  obtain ⟨τ, hτ⟩ := W.exists_isMin_tauObjective α qb
  exact ⟨τ, hτ⟩

/-- Additive decomposition of compactified pairings for `0 ≤ μ ≤ qb`. -/
theorem tauPair_add_sub {μ qb : ι → ℝ} (hμ0 : 0 ≤ μ) (hμle : μ ≤ qb)
    (τ : ι → ENNReal) :
    tauPair μ τ + tauPair (qb - μ) τ = tauPair qb τ := by
  unfold tauPair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← add_mul]
  congr 1
  change ENNReal.ofReal (μ i) + ENNReal.ofReal (qb i - μ i) = ENNReal.ofReal (qb i)
  rw [← ENNReal.ofReal_add (hμ0 i) (sub_nonneg.mpr (hμle i))]
  congr 1
  ring

/-- Extended Fenchel--Young tightness: `μ` attains the supremum defining
`G(α-τ)`.  This is the convention-safe compactified meaning of
`α - τ ∈ ∂G*(μ)`. -/
def ExtTight (α μ : ι → ℝ) (τ : ι → ENNReal) : Prop :=
  W.Gext α τ = W.extPayoff α μ τ

/-- Compactified complementary slackness. -/
def TauSlack (qb μ : ι → ℝ) (τ : ι → ENNReal) : Prop :=
  tauPair (qb - μ) τ = 0

/-- Compactified KKT sufficiency: exact extended Fenchel--Young tightness and
`0·∞` complementary slackness characterize a minimizer and give its value. -/
theorem tauObjective_eq_of_kkt
    (hDpos : ∀ ν ∈ W.D, 0 ≤ ν) (α : ι → ℝ)
    {qb μ : ι → ℝ} (hqb : 0 ≤ qb) (hμD : μ ∈ W.D) (hμle : μ ≤ qb)
    {τ : ι → ENNReal} (htight : W.ExtTight α μ τ)
    (hslack : TauSlack qb μ τ) :
    W.tauObjective α qb τ = ((W.boxValue α qb : ℝ) : EReal) ∧
      τ ∈ W.tauMinSet α qb := by
  have hμ0 := hDpos μ hμD
  have hpairs := tauPair_add_sub hμ0 hμle τ
  rw [hslack, add_zero] at hpairs
  have hpaybot : W.extPayoff α μ τ ≠ ⊥ := by
    rw [← htight]
    exact W.Gext_ne_bot α τ
  have hμtop : tauPair μ τ ≠ ⊤ := by
    intro htop
    apply hpaybot
    unfold extPayoff
    rw [htop]
    simp
  have hobj : W.tauObjective α qb τ =
      ((μ ⬝ᵥ α - W.cost μ : ℝ) : EReal) := by
    unfold tauObjective
    change W.Gext α τ = W.extPayoff α μ τ at htight
    rw [htight, ← hpairs]
    unfold extPayoff
    rw [← EReal.coe_ennreal_toReal hμtop, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    ring
  have hbox : W.boxValue α qb = μ ⬝ᵥ α - W.cost μ := by
    apply le_antisymm
    · have hw := W.boxValue_le_tauObjective hDpos α hqb τ
      rw [hobj] at hw
      exact EReal.coe_le_coe_iff.mp hw
    · exact W.le_boxValue α hqb hμD hμle
  constructor
  · rw [hobj, hbox]
  · intro τ'
    rw [hobj, ← hbox]
    exact W.boxValue_le_tauObjective hDpos α hqb τ'

/-- Compactified KKT necessity.  An attained waiting-time minimizer paired
with a box optimizer is extended Fenchel--Young tight and complementary. -/
theorem kkt_of_tauMin
    (hDpos : ∀ ν ∈ W.D, 0 ≤ ν) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ)
    {qb μ : ι → ℝ} (hqb : 0 ≤ qb) (hμD : μ ∈ W.D) (hμle : μ ≤ qb)
    (hopt : W.boxValue α qb = μ ⬝ᵥ α - W.cost μ)
    {τ : ι → ENNReal} (hmin : τ ∈ W.tauMinSet α qb) :
    W.ExtTight α μ τ ∧ TauSlack qb μ τ := by
  obtain ⟨τ₀, hτ₀val, hτ₀min⟩ :=
    W.exists_tauObjective_eq_boxValue hDpos hDconv hcost_conv α hqb
  have hobj : W.tauObjective α qb τ =
      ((μ ⬝ᵥ α - W.cost μ : ℝ) : EReal) := by
    rw [← hopt]
    apply le_antisymm
    · rw [← hτ₀val]
      exact hmin τ₀
    · exact W.boxValue_le_tauObjective hDpos α hqb τ
  have hqtop : tauPair qb τ ≠ ⊤ := by
    intro htop
    have he : W.tauObjective α qb τ = ⊤ := by
      unfold tauObjective
      have hp : (tauPair qb τ : EReal) = ⊤ := by rw [htop]; rfl
      rw [hp, EReal.top_add_of_ne_bot (W.Gext_ne_bot α τ)]
    rw [he] at hobj
    exact (EReal.top_ne_coe _) hobj
  have hGtop : W.Gext α τ ≠ ⊤ := by
    intro htop
    have he : W.tauObjective α qb τ = ⊤ := by
      unfold tauObjective
      rw [htop, EReal.add_top_of_ne_bot (by simp : (tauPair qb τ : EReal) ≠ ⊥)]
    rw [he] at hobj
    exact (EReal.top_ne_coe _) hobj
  have hGbot := W.Gext_ne_bot α τ
  lift W.Gext α τ to ℝ using ⟨hGtop, hGbot⟩ with g hg
  have hμ0 := hDpos μ hμD
  have hpair : tauPair μ τ ≤ tauPair qb τ := by
    unfold tauPair
    refine Finset.sum_le_sum fun i _ => ?_
    gcongr
    exact hμle i
  have hμtop : tauPair μ τ ≠ ⊤ := ne_top_of_le_ne_top hqtop hpair
  have hsum : (tauPair qb τ).toReal + g = μ ⬝ᵥ α - W.cost μ := by
    have h := hobj
    unfold tauObjective at h
    rw [← hg, ← EReal.coe_ennreal_toReal hqtop, ← EReal.coe_add] at h
    exact EReal.coe_eq_coe_iff.mp h
  have hpay : W.extPayoff α (⟨μ, hμD⟩ : W.D) τ ≤ W.Gext α τ :=
    le_iSup (fun ν : W.D => W.extPayoff α ν τ) ⟨μ, hμD⟩
  have hpayReal : μ ⬝ᵥ α - W.cost μ - (tauPair μ τ).toReal ≤ g := by
    unfold extPayoff at hpay
    rw [← hg, ← EReal.coe_ennreal_toReal hμtop, ← EReal.coe_sub,
      EReal.coe_le_coe_iff] at hpay
    exact hpay
  have hpairReal : (tauPair μ τ).toReal ≤ (tauPair qb τ).toReal :=
    ENNReal.toReal_mono hqtop hpair
  have hpairsEq : tauPair μ τ = tauPair qb τ := by
    exact (ENNReal.toReal_eq_toReal_iff' hμtop hqtop).mp (by linarith)
  have htight : W.ExtTight α μ τ := by
    change W.Gext α τ = W.extPayoff α μ τ
    rw [← hg]
    unfold extPayoff
    rw [← EReal.coe_ennreal_toReal hμtop, ← EReal.coe_sub]
    congr 1
    linarith
  have hslack : TauSlack qb μ τ := by
    change tauPair (qb - μ) τ = 0
    have hdecomp := tauPair_add_sub hμ0 hμle τ
    rw [hpairsEq] at hdecomp
    have hsle : tauPair (qb - μ) τ ≤ tauPair qb τ := by
      rw [← hdecomp]
      exact le_add_left le_rfl
    have hstop : tauPair (qb - μ) τ ≠ ⊤ := ne_top_of_le_ne_top hqtop hsle
    have hre := congrArg ENNReal.toReal hdecomp
    rw [ENNReal.toReal_add hqtop hstop] at hre
    rcases (ENNReal.toReal_eq_zero_iff (tauPair (qb - μ) τ)).mp (by linarith) with h | h
    · exact h
    · exact (hstop h).elim
  exact ⟨htight, hslack⟩

/-- **Lemma 2, exact compactified form.** For a box-optimal `μ`, the
compactified minimizers are exactly the extended-tight, complementary waiting
times. -/
theorem mem_tauMinSet_iff_kkt
    (hDpos : ∀ ν ∈ W.D, 0 ≤ ν) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ)
    {qb μ : ι → ℝ} (hqb : 0 ≤ qb) (hμD : μ ∈ W.D) (hμle : μ ≤ qb)
    (hopt : W.boxValue α qb = μ ⬝ᵥ α - W.cost μ)
    (τ : ι → ENNReal) :
    τ ∈ W.tauMinSet α qb ↔ W.ExtTight α μ τ ∧ TauSlack qb μ τ := by
  constructor
  · exact W.kkt_of_tauMin hDpos hDconv hcost_conv α hqb hμD hμle hopt
  · rintro ⟨htight, hslack⟩
    exact (W.tauObjective_eq_of_kkt hDpos α hqb hμD hμle htight hslack).2

/-! ## Submodularity of welfare from exchangeability -/

open Classical in
noncomputable def tauExDelta (p p' q₁ q₂ : ι → ℝ) : ι → ℝ :=
  fun i => if 0 < p i - p' i then (q₁ - q₂)⁺ i else 0

theorem tauExDelta_mem (p p' q₁ q₂ : ι → ℝ) :
    tauExDelta p p' q₁ q₂ ∈ Icc 0 ((q₁ - q₂)⁺) := by
  constructor <;> intro i <;> unfold tauExDelta
  · split
    · exact posPart_nonneg _
    · exact le_rfl
  · split
    · exact le_rfl
    · exact posPart_nonneg _

theorem tau_dotProduct_exchange_bound (p p' q₁ q₂ δ₂ : ι → ℝ)
    (hδ₂ : δ₂ ∈ Icc 0 ((q₁ - q₂)⁻)) :
    q₂ ⬝ᵥ (p ⊓ p') + q₁ ⬝ᵥ (p ⊔ p') ≤
      (q₂ + (tauExDelta p p' q₁ q₂ - δ₂)) ⬝ᵥ p +
        (q₁ - (tauExDelta p p' q₁ q₂ - δ₂)) ⬝ᵥ p' := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := coord_exchange (p i) (p' i) (q₁ i) (q₂ i) (δ₂ i)
    (hδ₂.1 i) (hδ₂.2 i)
  simpa [tauExDelta, Pi.add_apply, Pi.sub_apply, Pi.inf_apply, Pi.sup_apply] using h

/-- Exchangeability of the dual cost implies submodularity of the real welfare
function `Gfn`.  This is the arbitrary-finite-index version of Theorem 2's
elementary Q-to-P conjugacy direction. -/
theorem Gfn_submodular (hc : Exchangeable W.cFn) (p p' : ι → ℝ) :
    W.Gfn (p ⊓ p') + W.Gfn (p ⊔ p') ≤ W.Gfn p + W.Gfn p' := by
  obtain ⟨q₂, hq₂D, hmax₂, heq₂⟩ := W.exists_isMaxOn_Gfn (p ⊓ p')
  obtain ⟨q₁, hq₁D, hmax₁, heq₁⟩ := W.exists_isMaxOn_Gfn (p ⊔ p')
  obtain ⟨δ₂, hδ₂, hkey⟩ := hc q₁ q₂ (tauExDelta p p' q₁ q₂)
    (tauExDelta_mem p p' q₁ q₂)
  let d := tauExDelta p p' q₁ q₂ - δ₂
  have hq₁m : q₁ - d ∈ W.D := by
    by_contra hnot
    rw [W.cFn_of_not_mem hnot, top_add] at hkey
    rw [W.cFn_of_mem hq₁D, W.cFn_of_mem hq₂D, ← WithTop.coe_add] at hkey
    exact WithTop.coe_ne_top (top_le_iff.mp hkey)
  have hq₂m : q₂ + d ∈ W.D := by
    by_contra hnot
    rw [W.cFn_of_not_mem hnot, add_top] at hkey
    rw [W.cFn_of_mem hq₁D, W.cFn_of_mem hq₂D, ← WithTop.coe_add] at hkey
    exact WithTop.coe_ne_top (top_le_iff.mp hkey)
  have hcost : W.cost (q₁ - d) + W.cost (q₂ + d) ≤ W.cost q₁ + W.cost q₂ := by
    rw [W.cFn_of_mem hq₁m, W.cFn_of_mem hq₂m,
      W.cFn_of_mem hq₁D, W.cFn_of_mem hq₂D,
      ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hkey
    exact hkey
  have hp := W.le_Gfn (β := p) hq₂m
  have hp' := W.le_Gfn (β := p') hq₁m
  have hdot := tau_dotProduct_exchange_bound p p' q₁ q₂ δ₂ hδ₂
  change q₂ ⬝ᵥ (p ⊓ p') + q₁ ⬝ᵥ (p ⊔ p') ≤
      (q₂ + d) ⬝ᵥ p + (q₁ - d) ⬝ᵥ p' at hdot
  rw [heq₂, heq₁]
  linarith

theorem ennreal_transfer_le₁ {a b r : ℝ} {s t : ENNReal}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hra : r ≤ a) (hst : s ≤ t) :
    ENNReal.ofReal (a - r) * t + ENNReal.ofReal (b + r) * s ≤
      ENNReal.ofReal a * t + ENNReal.ofReal b * s := by
  have har : 0 ≤ a - r := sub_nonneg.mpr hra
  have hea : ENNReal.ofReal a = ENNReal.ofReal (a - r) + ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_add har hr]
    congr 1
    ring
  have heb : ENNReal.ofReal (b + r) = ENNReal.ofReal b + ENNReal.ofReal r :=
    ENNReal.ofReal_add hb hr
  rw [hea, heb]
  calc
    ENNReal.ofReal (a - r) * t +
        (ENNReal.ofReal b + ENNReal.ofReal r) * s =
      (ENNReal.ofReal (a - r) * t + ENNReal.ofReal b * s) +
        ENNReal.ofReal r * s := by ring
    _ ≤ (ENNReal.ofReal (a - r) * t + ENNReal.ofReal b * s) +
        ENNReal.ofReal r * t := by gcongr
    _ = (ENNReal.ofReal (a - r) + ENNReal.ofReal r) * t +
        ENNReal.ofReal b * s := by ring

theorem ennreal_transfer_le₂ {a b r : ℝ} {s t : ENNReal}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hrb : r ≤ b) (hst : s ≤ t) :
    ENNReal.ofReal (a + r) * s + ENNReal.ofReal (b - r) * t ≤
      ENNReal.ofReal a * s + ENNReal.ofReal b * t := by
  have hbr : 0 ≤ b - r := sub_nonneg.mpr hrb
  have hea : ENNReal.ofReal (a + r) = ENNReal.ofReal a + ENNReal.ofReal r :=
    ENNReal.ofReal_add ha hr
  have heb : ENNReal.ofReal b = ENNReal.ofReal (b - r) + ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_add hbr hr]
    congr 1
    ring
  rw [hea, heb]
  calc
    (ENNReal.ofReal a + ENNReal.ofReal r) * s +
        ENNReal.ofReal (b - r) * t =
      (ENNReal.ofReal a * s + ENNReal.ofReal (b - r) * t) +
        ENNReal.ofReal r * s := by ring
    _ ≤ (ENNReal.ofReal a * s + ENNReal.ofReal (b - r) * t) +
        ENNReal.ofReal r * t := by gcongr
    _ = ENNReal.ofReal a * s +
        (ENNReal.ofReal (b - r) + ENNReal.ofReal r) * t := by ring

open Classical in
noncomputable def tauExDeltaCompact
    (τ σ : ι → ENNReal) (q₁ q₂ : ι → ℝ) : ι → ℝ :=
  fun i => if τ i < σ i then (q₁ - q₂)⁺ i else 0

theorem tauExDeltaCompact_mem (τ σ : ι → ENNReal) (q₁ q₂ : ι → ℝ) :
    tauExDeltaCompact τ σ q₁ q₂ ∈ Icc 0 ((q₁ - q₂)⁺) := by
  constructor <;> intro i <;> unfold tauExDeltaCompact
  · split
    · exact posPart_nonneg _
    · exact le_rfl
  · split
    · exact le_rfl
    · exact posPart_nonneg _

theorem tauPair_exchange_bound
    (τ σ : ι → ENNReal) (q₁ q₂ δ₂ : ι → ℝ)
    (hδ₂ : δ₂ ∈ Icc 0 ((q₁ - q₂)⁻))
    (hq₁0 : 0 ≤ q₁) (hq₂0 : 0 ≤ q₂)
    (hq₁ : 0 ≤ q₁ - (tauExDeltaCompact τ σ q₁ q₂ - δ₂))
    (hq₂ : 0 ≤ q₂ + (tauExDeltaCompact τ σ q₁ q₂ - δ₂)) :
    tauPair (q₂ + (tauExDeltaCompact τ σ q₁ q₂ - δ₂)) τ +
        tauPair (q₁ - (tauExDeltaCompact τ σ q₁ q₂ - δ₂)) σ ≤
      tauPair q₂ (τ ⊔ σ) + tauPair q₁ (τ ⊓ σ) := by
  unfold tauPair
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hts : τ i < σ i
  · have hst : τ i ≤ σ i := hts.le
    let r : ℝ := (q₁ i - q₂ i)⁻ - δ₂ i
    have hr : 0 ≤ r := by
      dsimp [r]
      have hdle : δ₂ i ≤ (q₁ i - q₂ i)⁻ := hδ₂.2 i
      linarith
    have hrq₂ : r ≤ q₂ i := by
      have hm := hq₁ i
      simp only [Pi.sub_apply, Pi.add_apply, tauExDeltaCompact, if_pos hts,
        posPart_apply] at hm
      have hsplit := posPart_sub_negPart (q₁ i - q₂ i)
      dsimp [r]
      have hm' : (0 : ℝ) ≤ q₁ i - ((q₁ i - q₂ i)⁺ - δ₂ i) := hm
      linarith
    have h := ennreal_transfer_le₂ (hq₁0 i) hr hrq₂ hst
    simp only [Pi.add_apply, Pi.sub_apply, Pi.sup_apply, Pi.inf_apply,
      sup_eq_right.mpr hst, inf_eq_left.mpr hst,
      tauExDeltaCompact, if_pos hts, posPart_apply] at ⊢
    have hsplit := posPart_sub_negPart (q₁ i - q₂ i)
    dsimp [r] at h
    have he1 : q₂ i + ((q₁ i - q₂ i)⁺ - δ₂ i) =
        q₁ i + ((q₁ i - q₂ i)⁻ - δ₂ i) := by linarith
    have he2 : q₁ i - ((q₁ i - q₂ i)⁺ - δ₂ i) =
        q₂ i - ((q₁ i - q₂ i)⁻ - δ₂ i) := by linarith
    rw [he1, he2]
    simpa [add_comm] using h
  · have hst : σ i ≤ τ i := le_of_not_gt hts
    have hr : (0 : ℝ) ≤ δ₂ i := hδ₂.1 i
    have hrq₂ : δ₂ i ≤ q₂ i := by
      have hm := hq₂ i
      simp only [Pi.add_apply, Pi.sub_apply, tauExDeltaCompact, if_neg hts] at hm
      have hm' : (0 : ℝ) ≤ q₂ i + (0 - δ₂ i) := hm
      linarith
    have h := ennreal_transfer_le₁ (hq₂0 i) (hq₁0 i) hr hrq₂ hst
    simp only [Pi.add_apply, Pi.sub_apply, Pi.sup_apply, Pi.inf_apply,
      sup_eq_left.mpr hst, inf_eq_right.mpr hst,
      tauExDeltaCompact, if_neg hts] at ⊢
    simpa only [zero_sub, sub_neg_eq_add, add_neg_cancel_right] using h

theorem extPayoff_exchange (hc : Exchangeable W.cFn)
    (hDpos : ∀ q ∈ W.D, 0 ≤ q) (α : ι → ℝ) (τ σ : ι → ENNReal)
    (q₁ q₂ : W.D) :
    W.extPayoff α q₁ (τ ⊓ σ) + W.extPayoff α q₂ (τ ⊔ σ) ≤
      W.Gext α τ + W.Gext α σ := by
  obtain ⟨δ₂, hδ₂, hkey⟩ := hc q₁ q₂ (tauExDeltaCompact τ σ q₁ q₂)
    (tauExDeltaCompact_mem τ σ q₁ q₂)
  let d := tauExDeltaCompact τ σ (q₁ : ι → ℝ) q₂ - δ₂
  have hq₁m : (q₁ : ι → ℝ) - d ∈ W.D := by
    by_contra hnot
    rw [W.cFn_of_not_mem hnot, top_add] at hkey
    rw [W.cFn_of_mem q₁.property, W.cFn_of_mem q₂.property,
      ← WithTop.coe_add] at hkey
    exact WithTop.coe_ne_top (top_le_iff.mp hkey)
  have hq₂m : (q₂ : ι → ℝ) + d ∈ W.D := by
    by_contra hnot
    rw [W.cFn_of_not_mem hnot, add_top] at hkey
    rw [W.cFn_of_mem q₁.property, W.cFn_of_mem q₂.property,
      ← WithTop.coe_add] at hkey
    exact WithTop.coe_ne_top (top_le_iff.mp hkey)
  have hcost : W.cost ((q₁ : ι → ℝ) - d) + W.cost ((q₂ : ι → ℝ) + d) ≤
      W.cost q₁ + W.cost q₂ := by
    rw [W.cFn_of_mem hq₁m, W.cFn_of_mem hq₂m,
      W.cFn_of_mem q₁.property, W.cFn_of_mem q₂.property,
      ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hkey
    exact hkey
  have hq₁0 := hDpos q₁ q₁.property
  have hq₂0 := hDpos q₂ q₂.property
  have hq₁m0 := hDpos _ hq₁m
  have hq₂m0 := hDpos _ hq₂m
  have hpen := tauPair_exchange_bound τ σ (q₁ : ι → ℝ) q₂ δ₂ hδ₂
    hq₁0 hq₂0 hq₁m0 hq₂m0
  change tauPair ((q₂ : ι → ℝ) + d) τ + tauPair ((q₁ : ι → ℝ) - d) σ ≤
      tauPair q₂ (τ ⊔ σ) + tauPair q₁ (τ ⊓ σ) at hpen
  have hbase : q₂ ⬝ᵥ α - W.cost q₂ + (q₁ ⬝ᵥ α - W.cost q₁) ≤
      ((q₂ : ι → ℝ) + d) ⬝ᵥ α - W.cost ((q₂ : ι → ℝ) + d) +
        (((q₁ : ι → ℝ) - d) ⬝ᵥ α - W.cost ((q₁ : ι → ℝ) - d)) := by
    have hmass : ((q₂ : ι → ℝ) + d) ⬝ᵥ α + ((q₁ : ι → ℝ) - d) ⬝ᵥ α =
        q₂ ⬝ᵥ α + q₁ ⬝ᵥ α := by
      rw [add_dotProduct (q₂ : ι → ℝ) d α,
        sub_dotProduct (q₁ : ι → ℝ) d α]
      ring
    linarith
  by_cases hL1 : tauPair (q₁ : ι → ℝ) (τ ⊓ σ) = ⊤
  · unfold extPayoff
    rw [hL1]
    simp
  by_cases hL2 : tauPair (q₂ : ι → ℝ) (τ ⊔ σ) = ⊤
  · unfold extPayoff
    rw [hL2]
    simp
  have hLtop : tauPair q₂ (τ ⊔ σ) + tauPair q₁ (τ ⊓ σ) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨hL2, hL1⟩
  have hRtop : tauPair ((q₂ : ι → ℝ) + d) τ +
      tauPair ((q₁ : ι → ℝ) - d) σ ≠ ⊤ := ne_top_of_le_ne_top hLtop hpen
  have hR2 : tauPair ((q₂ : ι → ℝ) + d) τ ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hRtop).1
  have hR1 : tauPair ((q₁ : ι → ℝ) - d) σ ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hRtop).2
  have hpenReal := ENNReal.toReal_mono hLtop hpen
  rw [ENNReal.toReal_add hR2 hR1,
    ENNReal.toReal_add hL2 hL1] at hpenReal
  have hmove : W.extPayoff α ((q₂ : ι → ℝ) + d) τ +
      W.extPayoff α ((q₁ : ι → ℝ) - d) σ ≤ W.Gext α τ + W.Gext α σ :=
    add_le_add
      (le_iSup (fun q : W.D => W.extPayoff α q τ) ⟨_, hq₂m⟩)
      (le_iSup (fun q : W.D => W.extPayoff α q σ) ⟨_, hq₁m⟩)
  refine le_trans ?_ hmove
  unfold extPayoff
  rw [← EReal.coe_ennreal_toReal hL1, ← EReal.coe_ennreal_toReal hL2,
    ← EReal.coe_ennreal_toReal hR2, ← EReal.coe_ennreal_toReal hR1,
    ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

theorem Gext_le_Gfn (hDpos : ∀ q ∈ W.D, 0 ≤ q)
    (α : ι → ℝ) (τ : ι → ENNReal) :
    W.Gext α τ ≤ ((W.Gfn α : ℝ) : EReal) := by
  unfold Gext
  refine iSup_le fun q => ?_
  have hbase : q ⬝ᵥ α - W.cost q ≤ W.Gfn α := W.le_Gfn q.property
  unfold extPayoff
  by_cases hp : tauPair (q : ι → ℝ) τ = ⊤
  · rw [hp]
    simp
  rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_sub,
    EReal.coe_le_coe_iff]
  have hnonneg : 0 ≤ (tauPair (q : ι → ℝ) τ).toReal := ENNReal.toReal_nonneg
  linarith

theorem Gext_ne_top (hDpos : ∀ q ∈ W.D, 0 ≤ q)
    (α : ι → ℝ) (τ : ι → ENNReal) : W.Gext α τ ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (W.Gext_le_Gfn hDpos α τ)

/-- The supremum-formula welfare remains submodular on compactified waiting
times.  This is the extended-real Q-to-P conjugacy step. -/
theorem Gext_submodular (hc : Exchangeable W.cFn)
    (hDpos : ∀ q ∈ W.D, 0 ≤ q) (α : ι → ℝ) (τ σ : ι → ENNReal) :
    W.Gext α (τ ⊓ σ) + W.Gext α (τ ⊔ σ) ≤
      W.Gext α τ + W.Gext α σ := by
  unfold Gext
  rw [section16_iSup_add_iSup_eq_iSup_prod]
  refine iSup_le fun q => ?_
  exact W.extPayoff_exchange hc hDpos α τ σ q.1 q.2

theorem tauPair_cross_le {qh ql : ι → ℝ} (hql0 : 0 ≤ ql)
    (hqlh : ql ≤ qh) (τ σ : ι → ENNReal) :
    tauPair qh (τ ⊓ σ) + tauPair ql (τ ⊔ σ) ≤
      tauPair qh τ + tauPair ql σ := by
  unfold tauPair
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_total (τ i) (σ i) with hts | hst
  · simp only [Pi.inf_apply, Pi.sup_apply, inf_eq_left.mpr hts, sup_eq_right.mpr hts]
    exact le_rfl
  · simp only [Pi.inf_apply, Pi.sup_apply, inf_eq_right.mpr hst, sup_eq_left.mpr hst]
    let r := qh i - ql i
    have hr : 0 ≤ r := sub_nonneg.mpr (hqlh i)
    have hqh : ENNReal.ofReal (qh i) = ENNReal.ofReal (ql i) + ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add (hql0 i) hr]
      congr 1
      dsimp [r]
      ring
    rw [hqh]
    calc
      (ENNReal.ofReal (ql i) + ENNReal.ofReal r) * σ i +
          ENNReal.ofReal (ql i) * τ i =
        (ENNReal.ofReal (ql i) * σ i + ENNReal.ofReal (ql i) * τ i) +
          ENNReal.ofReal r * σ i := by ring
      _ ≤ (ENNReal.ofReal (ql i) * σ i + ENNReal.ofReal (ql i) * τ i) +
          ENNReal.ofReal r * τ i := by gcongr
      _ = (ENNReal.ofReal (ql i) + ENNReal.ofReal r) * τ i +
          ENNReal.ofReal (ql i) * σ i := by ring

private theorem ereal_ennreal_add_reassoc {a b : ENNReal} {x y : EReal}
    (hxtop : x ≠ ⊤) (hxbot : x ≠ ⊥) (hytop : y ≠ ⊤) (hybot : y ≠ ⊥) :
    ((a : EReal) + x) + ((b : EReal) + y) = ((a + b : ENNReal) : EReal) + (x + y) := by
  lift x to ℝ using ⟨hxtop, hxbot⟩ with xr hxr
  lift y to ℝ using ⟨hytop, hybot⟩ with yr hyr
  by_cases ha : a = ⊤
  · subst a
    simp
  by_cases hb : b = ⊤
  · subst b
    simp
  lift a to NNReal using ha with ar har
  lift b to NNReal using hb with br hbr
  simp only [EReal.coe_nnreal_eq_coe_real]
  rw [← EReal.coe_add]
  exact congrArg ((↑) : ℝ → EReal) (by
    change ((ar : ℝ) + xr) + ((br : ℝ) + yr) = ((ar + br : NNReal) : ℝ) + (xr + yr)
    rw [NNReal.coe_add]
    ring)

/-- Increasing differences of the compactified objective in waiting times
and the negative capacity parameter. -/
theorem tauObjective_pOrder (hc : Exchangeable W.cFn)
    (hDpos : ∀ q ∈ W.D, 0 ≤ q) (α : ι → ℝ)
    {ql qh : ι → ℝ} (hql0 : 0 ≤ ql) (hqlh : ql ≤ qh)
    (τ σ : ι → ENNReal) :
    W.tauObjective α qh (τ ⊓ σ) + W.tauObjective α ql (τ ⊔ σ) ≤
      W.tauObjective α qh τ + W.tauObjective α ql σ := by
  have hp := tauPair_cross_le hql0 hqlh τ σ
  have hG := W.Gext_submodular hc hDpos α τ σ
  have hmt := W.Gext_ne_top hDpos α (τ ⊓ σ)
  have hmb := W.Gext_ne_bot α (τ ⊓ σ)
  have hjt := W.Gext_ne_top hDpos α (τ ⊔ σ)
  have hjb := W.Gext_ne_bot α (τ ⊔ σ)
  have htt := W.Gext_ne_top hDpos α τ
  have htb := W.Gext_ne_bot α τ
  have hst := W.Gext_ne_top hDpos α σ
  have hsb := W.Gext_ne_bot α σ
  unfold tauObjective
  calc
    ((tauPair qh (τ ⊓ σ) : EReal) + W.Gext α (τ ⊓ σ)) +
        ((tauPair ql (τ ⊔ σ) : EReal) + W.Gext α (τ ⊔ σ)) =
      ((tauPair qh (τ ⊓ σ) + tauPair ql (τ ⊔ σ) : ENNReal) : EReal) +
        (W.Gext α (τ ⊓ σ) + W.Gext α (τ ⊔ σ)) :=
      ereal_ennreal_add_reassoc hmt hmb hjt hjb
    _ ≤ ((tauPair qh τ + tauPair ql σ : ENNReal) : EReal) +
        (W.Gext α τ + W.Gext α σ) := by
          apply add_le_add
          · exact_mod_cast hp
          · exact hG
    _ = ((tauPair qh τ : EReal) + W.Gext α τ) +
        ((tauPair ql σ : EReal) + W.Gext α σ) :=
      (ereal_ennreal_add_reassoc htt htb hst hsb).symm

def TauPOrderSet (X Y : Set (ι → ENNReal)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ⊓ y ∈ X ∧ x ⊔ y ∈ Y

theorem ereal_eq_of_le_of_le_of_add_le_add {a b c d : EReal}
    (hctop : c ≠ ⊤) (hcbot : c ≠ ⊥) (hdtop : d ≠ ⊤) (hdbot : d ≠ ⊥)
    (hca : c ≤ a) (hdb : d ≤ b) (h : a + b ≤ c + d) : a = c ∧ b = d := by
  lift c to ℝ using ⟨hctop, hcbot⟩ with cr hcr
  lift d to ℝ using ⟨hdtop, hdbot⟩ with dr hdr
  have habot : a ≠ ⊥ := ne_bot_of_gt ((EReal.bot_lt_coe cr).trans_le hca)
  have hbbot : b ≠ ⊥ := ne_bot_of_gt ((EReal.bot_lt_coe dr).trans_le hdb)
  have hatop : a ≠ ⊤ := by
    intro ha
    rw [ha, EReal.top_add_of_ne_bot hbbot, ← EReal.coe_add] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  have hbtop : b ≠ ⊤ := by
    intro hb
    rw [hb, EReal.add_top_of_ne_bot habot, ← EReal.coe_add] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  lift a to ℝ using ⟨hatop, habot⟩ with ar har
  lift b to ℝ using ⟨hbtop, hbbot⟩ with br hbr
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [EReal.coe_le_coe_iff] at hca hdb
  constructor <;> congr 1 <;> linarith

/-- Exact compactified Topkis: higher capacities select the meet into the
higher-capacity minimizer set and the join into the lower-capacity set. -/
theorem tauMinSet_pOrder (hc : Exchangeable W.cFn)
    (hDpos : ∀ q ∈ W.D, 0 ≤ q) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ)
    {ql qh : ι → ℝ} (hql0 : 0 ≤ ql) (hqlh : ql ≤ qh) :
    TauPOrderSet (W.tauMinSet α qh) (W.tauMinSet α ql) := by
  intro x hx y hy
  have hqh0 : 0 ≤ qh := fun i => (hql0 i).trans (hqlh i)
  obtain ⟨xh, hxhval, -⟩ :=
    W.exists_tauObjective_eq_boxValue hDpos hDconv hcost_conv α hqh0
  obtain ⟨yl, hylval, -⟩ :=
    W.exists_tauObjective_eq_boxValue hDpos hDconv hcost_conv α hql0
  have hxval : W.tauObjective α qh x = ((W.boxValue α qh : ℝ) : EReal) := by
    apply le_antisymm
    · rw [← hxhval]
      exact hx xh
    · exact W.boxValue_le_tauObjective hDpos α hqh0 x
  have hyval : W.tauObjective α ql y = ((W.boxValue α ql : ℝ) : EReal) := by
    apply le_antisymm
    · rw [← hylval]
      exact hy yl
    · exact W.boxValue_le_tauObjective hDpos α hql0 y
  have hcross := W.tauObjective_pOrder hc hDpos α hql0 hqlh x y
  have hmeet : W.tauObjective α qh x ≤ W.tauObjective α qh (x ⊓ y) := hx _
  have hjoin : W.tauObjective α ql y ≤ W.tauObjective α ql (x ⊔ y) := hy _
  have heq := ereal_eq_of_le_of_le_of_add_le_add
    (a := W.tauObjective α qh (x ⊓ y))
    (b := W.tauObjective α ql (x ⊔ y))
    (c := W.tauObjective α qh x) (d := W.tauObjective α ql y)
    (by rw [hxval]; exact EReal.coe_ne_top _)
    (by rw [hxval]; exact EReal.coe_ne_bot _)
    (by rw [hyval]; exact EReal.coe_ne_top _)
    (by rw [hyval]; exact EReal.coe_ne_bot _)
    hmeet hjoin hcross
  constructor
  · intro z
    rw [heq.1]
    exact hx z
  · intro z
    rw [heq.2]
    exact hy z

/-- Coordinatewise infimum of a set of compactified waiting-time vectors. -/
noncomputable def tauSetInf (X : Set (ι → ENNReal)) : ι → ENNReal :=
  fun i => ⨅ x : X, x.1 i

/-- The canonical least-waiting-time vector used in Appendix C. -/
noncomputable def tauInf (α qb : ι → ℝ) : ι → ENNReal :=
  tauSetInf (W.tauMinSet α qb)

theorem tauSetInf_le_of_pOrder {X Y : Set (ι → ENNReal)}
    (hX : X.Nonempty) (hXY : TauPOrderSet X Y) :
    tauSetInf X ≤ tauSetInf Y := by
  intro i
  unfold tauSetInf
  refine le_iInf fun y => ?_
  obtain ⟨x, hx⟩ := hX
  have hm : x ⊓ y.1 ∈ X := (hXY x hx y.1 y.2).1
  calc
    (⨅ z : X, z.1 i) ≤ (⟨x ⊓ y.1, hm⟩ : X).1 i := iInf_le _ _
    _ ≤ y.1 i := by exact inf_le_right

/-- The coordinatewise infimum of exact waiting times is increasing when the
capacity decreases.  This is the order statement needed for the proposer
sequence in Lemma 3. -/
theorem tauInf_anti_capacity (hc : Exchangeable W.cFn)
    (hDpos : ∀ q ∈ W.D, 0 ≤ q) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ)
    {ql qh : ι → ℝ} (hql0 : 0 ≤ ql) (hqlh : ql ≤ qh) :
    W.tauInf α qh ≤ W.tauInf α ql := by
  exact tauSetInf_le_of_pOrder (W.tauMinSet_nonempty α qh)
    (W.tauMinSet_pOrder hc hDpos hDconv hcost_conv α hql0 hqlh)

theorem isClosed_tauMinSet (α qb : ι → ℝ) : IsClosed (W.tauMinSet α qb) := by
  obtain ⟨x, hx⟩ := W.tauMinSet_nonempty α qb
  have heq : W.tauMinSet α qb =
      W.tauObjective α qb ⁻¹' Set.Iic (W.tauObjective α qb x) := by
    ext τ
    constructor
    · intro hτ
      exact hτ x
    · intro hτ z
      exact hτ.trans (hx z)
  rw [heq]
  exact (W.lowerSemicontinuous_tauObjective α qb).isClosed_preimage _

theorem isCompact_tauMinSet (α qb : ι → ℝ) : IsCompact (W.tauMinSet α qb) :=
  (W.isClosed_tauMinSet α qb).isCompact

theorem lowerSemicontinuous_tauPair_joint :
    LowerSemicontinuous fun z : (ι → ℝ) × (ι → ENNReal) => tauPair z.1 z.2 := by
  classical
  have hterm (i : ι) : LowerSemicontinuous fun z : (ι → ℝ) × (ι → ENNReal) =>
      ENNReal.ofReal (z.1 i) * z.2 i := by
    intro z
    by_cases hbad : ENNReal.ofReal (z.1 i) = 0 ∧ z.2 i = ⊤
    · intro y hy
      change y < ENNReal.ofReal (z.1 i) * z.2 i at hy
      rw [hbad.1, zero_mul] at hy
      exact (not_lt_of_ge bot_le hy).elim
    · have ha : Tendsto (fun w : (ι → ℝ) × (ι → ENNReal) =>
          ENNReal.ofReal (w.1 i)) (𝓝 z) (𝓝 (ENNReal.ofReal (z.1 i))) :=
        (ENNReal.continuous_ofReal.comp
          ((continuous_apply i).comp continuous_fst)).tendsto z
      have hb : Tendsto (fun w : (ι → ℝ) × (ι → ENNReal) => w.2 i)
          (𝓝 z) (𝓝 (z.2 i)) := ((continuous_apply i).comp continuous_snd).tendsto z
      have hc : ContinuousAt (fun w : (ι → ℝ) × (ι → ENNReal) =>
          ENNReal.ofReal (w.1 i) * w.2 i) z :=
        ENNReal.Tendsto.mul ha (not_and_or.mp hbad) hb
          (Or.inr ENNReal.ofReal_ne_top)
      exact hc.lowerSemicontinuousAt
  unfold tauPair
  induction (Finset.univ : Finset ι) using Finset.induction with
  | empty => simpa using (lowerSemicontinuous_const :
      LowerSemicontinuous (fun _ : (ι → ℝ) × (ι → ENNReal) => (0 : ENNReal)))
  | @insert i s hi ih =>
      simpa [Finset.sum_insert hi] using (hterm i).add ih

theorem lowerSemicontinuous_tauObjective_joint (α : ι → ℝ) :
    LowerSemicontinuous fun z : (ι → ℝ) × (ι → ENNReal) =>
      W.tauObjective α z.1 z.2 := by
  unfold tauObjective
  have hp : LowerSemicontinuous fun z : (ι → ℝ) × (ι → ENNReal) =>
      (tauPair z.1 z.2 : EReal) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      lowerSemicontinuous_tauPair_joint fun _ _ h =>
        EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  have hG : LowerSemicontinuous fun z : (ι → ℝ) × (ι → ENNReal) =>
      W.Gext α z.2 := (W.lowerSemicontinuous_Gext α).comp continuous_snd
  refine hp.add' hG fun z => ?_
  exact EReal.continuousAt_add (Or.inr (W.Gext_ne_bot α z.2))
    (Or.inl (by simp : (tauPair z.1 z.2 : EReal) ≠ ⊥))

/-- Closed graph of exact compactified waiting-time minimizers along
nonnegative capacities.  The proof tests against finite waiting times and
uses ε-strong duality, avoiding any continuity claim at `0 * ∞`. -/
theorem tauMinSet_limit
    (hDpos : ∀ μ ∈ W.D, 0 ≤ μ) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ)
    {qk : ℕ → ι → ℝ} {q : ι → ℝ} {τk : ℕ → ι → ENNReal}
    {τ : ι → ENNReal} (hqk0 : ∀ k, 0 ≤ qk k) (hq0 : 0 ≤ q)
    (hqlim : Tendsto qk atTop (𝓝 q)) (hτlim : Tendsto τk atTop (𝓝 τ))
    (hmin : ∀ k, τk k ∈ W.tauMinSet α (qk k)) :
    τ ∈ W.tauMinSet α q := by
  have htest (t : ι → ℝ) (ht0 : 0 ≤ t) :
      W.tauObjective α q τ ≤
        ((q ⬝ᵥ t + W.Gfn (α - t) : ℝ) : EReal) := by
    let rhs : (ι → ℝ) × (ι → ENNReal) → EReal := fun z =>
      ((z.1 ⬝ᵥ t + W.Gfn (α - t) : ℝ) : EReal)
    have hrhs : Continuous rhs := by
      apply continuous_coe_real_ereal.comp
      exact (continuous_finset_sum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul continuous_const).add
          continuous_const
    let F : (ι → ℝ) × (ι → ENNReal) → EReal := fun z =>
      W.tauObjective α z.1 z.2 - rhs z
    have hF : LowerSemicontinuous F := by
      show LowerSemicontinuous fun z =>
        W.tauObjective α z.1 z.2 + -(rhs z)
      refine (W.lowerSemicontinuous_tauObjective_joint α).add'
        (hrhs.neg.lowerSemicontinuous) fun z => ?_
      exact EReal.continuousAt_add
        (Or.inr (by
          change -(rhs z) ≠ ⊥
          have hr : rhs z = ((z.1 ⬝ᵥ t + W.Gfn (α - t) : ℝ) : EReal) := rfl
          intro h
          have ht := EReal.neg_eq_bot_iff.mp h
          rw [hr] at ht
          exact EReal.coe_ne_top _ ht))
        (Or.inr (by
          change -(rhs z) ≠ ⊤
          have hr : rhs z = ((z.1 ⬝ᵥ t + W.Gfn (α - t) : ℝ) : EReal) := rfl
          intro h
          have hb := EReal.neg_eq_top_iff.mp h
          rw [hr] at hb
          exact EReal.coe_ne_bot _ hb))
    have hclosed : IsClosed (F ⁻¹' Set.Iic 0) := hF.isClosed_preimage 0
    have hseq : ∀ k, (qk k, τk k) ∈ F ⁻¹' Set.Iic 0 := by
      intro k
      change F (qk k, τk k) ≤ 0
      rw [EReal.sub_nonpos]
      change W.tauObjective α (qk k) (τk k) ≤
        ((qk k ⬝ᵥ t + W.Gfn (α - t) : ℝ) : EReal)
      rw [← W.tauObjective_tauOfReal hDpos (hqk0 k) ht0]
      exact hmin k (tauOfReal t)
    have hpair : Tendsto (fun k => (qk k, τk k)) atTop (𝓝 (q, τ)) :=
      hqlim.prodMk_nhds hτlim
    have hlimmem := hclosed.mem_of_tendsto hpair (Eventually.of_forall hseq)
    change F (q, τ) ≤ 0 at hlimmem
    rw [EReal.sub_nonpos] at hlimmem
    exact hlimmem
  have hlower := W.boxValue_le_tauObjective hDpos α hq0 τ
  have hub (ε : ℝ) (hε : 0 < ε) :
      W.tauObjective α q τ ≤ ((W.boxValue α q + ε : ℝ) : EReal) := by
    obtain ⟨t, ht0, ht⟩ := W.exists_dual_near hDconv hcost_conv α hq0 hε
    exact (htest t ht0).trans (EReal.coe_le_coe_iff.mpr ht)
  have htop : W.tauObjective α q τ ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hub 1 one_pos)
  have hbot : W.tauObjective α q τ ≠ ⊥ :=
    ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) hlower)
  lift W.tauObjective α q τ to ℝ using ⟨htop, hbot⟩ with r hr
  have hrle : r ≤ W.boxValue α q := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact EReal.coe_le_coe_iff.mp (hub ε hε)
  have heq : W.tauObjective α q τ = ((W.boxValue α q : ℝ) : EReal) := by
    apply le_antisymm
    · rw [← hr]
      exact EReal.coe_le_coe_iff.mpr hrle
    · rw [← hr]
      exact hlower
  intro σ
  rw [heq]
  exact W.boxValue_le_tauObjective hDpos α hq0 σ

/-! ## Capacity-bound normalization -/

/-- Zero a waiting time on coordinates at which the matching saturates the
given side capacity. -/
noncomputable def normalizeTau (bound μ : ι → ℝ) (τ : ι → ENNReal) :
    ι → ENNReal := fun i => if μ i = bound i then 0 else τ i

private noncomputable def removedTau (bound μ : ι → ℝ) (τ : ι → ENNReal) :
    ι → ENNReal := fun i => if μ i = bound i then τ i else 0

private theorem tauPair_normalize_add_removed (a bound μ : ι → ℝ)
    (τ : ι → ENNReal) :
    tauPair a (normalizeTau bound μ τ) + tauPair a (removedTau bound μ τ) =
      tauPair a τ := by
  unfold tauPair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : μ i = bound i <;> simp [normalizeTau, removedTau, h]

private theorem tauPair_removed_mono {ν μ bound : ι → ℝ}
    (hν0 : 0 ≤ ν) (hνb : ν ≤ bound) (τ : ι → ENNReal) :
    tauPair ν (removedTau bound μ τ) ≤ tauPair μ (removedTau bound μ τ) := by
  unfold tauPair
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : μ i = bound i
  · simp only [removedTau, h, if_pos]
    gcongr
    exact hνb i
  · simp [removedTau, h]

/-- The paper's saturation normalization preserves extended
Fenchel--Young tightness.  The explicit domain bound is the missing
hypothesis used in Appendix C's final modification argument. -/
theorem extTight_normalize (hDpos : ∀ ν ∈ W.D, 0 ≤ ν)
    {bound α μ : ι → ℝ} (hμD : μ ∈ W.D)
    (hbound : ∀ ν ∈ W.D, ν ≤ bound) {τ : ι → ENNReal}
    (htight : W.ExtTight α μ τ) :
    W.ExtTight α μ (normalizeTau bound μ τ) := by
  have hμ0 := hDpos μ hμD
  have hμpairtop : tauPair μ τ ≠ ⊤ := by
    intro hp
    have : W.extPayoff α μ τ = ⊥ := by unfold extPayoff; rw [hp]; simp
    rw [← htight] at this
    exact W.Gext_ne_bot α τ this
  have hsplitμ := tauPair_normalize_add_removed μ bound μ τ
  have hKμtop : tauPair μ (removedTau bound μ τ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hμpairtop
    rw [← hsplitμ]
    exact le_add_left le_rfl
  apply le_antisymm
  · refine iSup_le fun ν => ?_
    have hν0 := hDpos ν ν.property
    have hKle := tauPair_removed_mono (μ := μ) hν0 (hbound ν ν.property) τ
    have hKνtop : tauPair ν (removedTau bound μ τ) ≠ ⊤ :=
      ne_top_of_le_ne_top hKμtop hKle
    have hbase : W.extPayoff α ν τ ≤ W.extPayoff α μ τ := by
      calc
        W.extPayoff α ν τ ≤ W.Gext α τ :=
          le_iSup (fun η : W.D => W.extPayoff α η τ) ν
        _ = W.extPayoff α μ τ := htight
    have hsplitν := tauPair_normalize_add_removed (ν : ι → ℝ) bound μ τ
    by_cases hνpairtop : tauPair ν τ = ⊤
    · have hDνtop : tauPair ν (normalizeTau bound μ τ) = ⊤ := by
        rw [← hsplitν] at hνpairtop
        exact (ENNReal.add_eq_top.mp hνpairtop).resolve_right hKνtop
      unfold extPayoff
      rw [hDνtop]
      simp
    · have hDνtop : tauPair ν (normalizeTau bound μ τ) ≠ ⊤ := by
        apply ne_top_of_le_ne_top hνpairtop
        rw [← hsplitν]
        exact le_add_right le_rfl
      have hDμtop : tauPair μ (normalizeTau bound μ τ) ≠ ⊤ := by
        apply ne_top_of_le_ne_top hμpairtop
        rw [← hsplitμ]
        exact le_add_right le_rfl
      have hKreal : (tauPair ν (removedTau bound μ τ)).toReal ≤
          (tauPair μ (removedTau bound μ τ)).toReal :=
        ENNReal.toReal_mono hKμtop hKle
      have hbaseReal :
          ν.1 ⬝ᵥ α - W.cost ν.1 - (tauPair ν τ).toReal ≤
            μ ⬝ᵥ α - W.cost μ - (tauPair μ τ).toReal := by
        unfold extPayoff at hbase
        rw [← EReal.coe_ennreal_toReal hνpairtop,
          ← EReal.coe_ennreal_toReal hμpairtop, ← EReal.coe_sub,
          ← EReal.coe_sub, EReal.coe_le_coe_iff] at hbase
        exact hbase
      have hsplitνReal := congrArg ENNReal.toReal hsplitν
      have hsplitμReal := congrArg ENNReal.toReal hsplitμ
      rw [ENNReal.toReal_add hDνtop hKνtop] at hsplitνReal
      rw [ENNReal.toReal_add hDμtop hKμtop] at hsplitμReal
      unfold extPayoff
      rw [← EReal.coe_ennreal_toReal hDνtop,
        ← EReal.coe_ennreal_toReal hDμtop, ← EReal.coe_sub, ← EReal.coe_sub,
        EReal.coe_le_coe_iff]
      linarith
  · exact le_iSup (fun ν : W.D =>
      W.extPayoff α ν (normalizeTau bound μ τ)) ⟨μ, hμD⟩

theorem tauSlack_normalize {qb μ bound : ι → ℝ} (hμle : μ ≤ qb)
    {τ : ι → ENNReal} (hslack : TauSlack qb μ τ) :
    TauSlack qb μ (normalizeTau bound μ τ) := by
  change tauPair (qb - μ) (normalizeTau bound μ τ) = 0
  apply le_antisymm
  · calc
      tauPair (qb - μ) (normalizeTau bound μ τ) ≤ tauPair (qb - μ) τ :=
        tauPair_mono_right (sub_nonneg.mpr hμle) (fun i => by
          simp only [normalizeTau]
          split <;> simp)
      _ = 0 := hslack
  · exact bot_le

theorem tau_eq_zero_of_slack_of_lt {qb μ : ι → ℝ} {τ : ι → ENNReal}
    (hslack : TauSlack qb μ τ) {i : ι} (hi : μ i < qb i) : τ i = 0 := by
  have hterm : ENNReal.ofReal (qb i - μ i) * τ i = 0 := by
    have hle : ENNReal.ofReal (qb i - μ i) * τ i ≤ tauPair (qb - μ) τ := by
      unfold tauPair
      exact Finset.single_le_sum (fun j _ => zero_le
        (ENNReal.ofReal ((qb - μ) j) * τ j)) (Finset.mem_univ i)
    rw [hslack] at hle
    exact bot_unique hle
  rcases mul_eq_zero.mp hterm with hcoef | hτ
  · rw [ENNReal.ofReal_eq_zero] at hcoef
    linarith
  · exact hτ

/-- The coordinatewise infimum is itself an attained exact waiting time.
Finiteness of the coordinate type is used only to meet together one
coordinate-minimizer for each coordinate. -/
theorem tauInf_mem (hc : Exchangeable W.cFn)
    (hDpos : ∀ q ∈ W.D, 0 ≤ q) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α qb : ι → ℝ) (hqb : 0 ≤ qb) :
    W.tauInf α qb ∈ W.tauMinSet α qb := by
  classical
  let X := W.tauMinSet α qb
  have hX : X.Nonempty := W.tauMinSet_nonempty α qb
  have hcompact : IsCompact X := W.isCompact_tauMinSet α qb
  have hinf : ∀ᵉ (x ∈ X) (y ∈ X), x ⊓ y ∈ X := by
    intro x hx y hy
    exact (W.tauMinSet_pOrder hc hDpos hDconv hcost_conv α hqb
      (fun _ => le_rfl) x hx y hy).1
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      obtain ⟨x, hx⟩ := hX
      exact (Subsingleton.elim (W.tauInf α qb) x) ▸ hx
  | inr hne =>
      letI := hne
      have hcoord (i : ι) :
          ∃ x ∈ X, ∀ y ∈ X, x i ≤ y i := by
        exact hcompact.exists_isMinOn hX (continuous_apply i).continuousOn
      choose p hpX hpmin using hcoord
      let m : ι → ENNReal := Finset.univ.inf' Finset.univ_nonempty p
      have hmX : m ∈ X :=
        Finset.inf'_mem X hinf Finset.univ Finset.univ_nonempty p
          (fun i _ => hpX i)
      have hmeq : m = W.tauInf α qb := by
        funext j
        apply le_antisymm
        · unfold tauInf tauSetInf
          refine le_iInf fun y => ?_
          have hmle : m ≤ p j := Finset.inf'_le p (Finset.mem_univ j)
          exact (hmle j).trans (hpmin j y.1 y.2)
        · unfold tauInf tauSetInf
          have hle : (fun k => ⨅ x : X, x.1 k) ≤ m := by
            refine Finset.le_inf' Finset.univ_nonempty p fun i _ k => ?_
            exact iInf_le_of_le (⟨p i, hpX i⟩ : X) le_rfl
          exact hle j
      rw [← hmeq]
      exact hmX

/-- **G4 at the level required by Lemma 3.** Tightening a capacity to an
optimal accepted mass leaves the *least* exact waiting time unchanged.
Unlike equality of dual values, this uses exact KKT and meet-closure of the
compactified multiplier set. -/
theorem tauInf_capacity_eq_of_opt (hc : Exchangeable W.cFn)
    (hDpos : ∀ q ∈ W.D, 0 ≤ q) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ)
    {qb μ : ι → ℝ} (hqb : 0 ≤ qb) (hμD : μ ∈ W.D) (hμle : μ ≤ qb)
    (hopt : W.boxValue α qb = μ ⬝ᵥ α - W.cost μ) :
    W.tauInf α μ = W.tauInf α qb := by
  have hμ0 := hDpos μ hμD
  have hcap := W.boxValue_capacity_eq_of_opt α hqb hμ0 hμD hμle hopt
  have hoptμ : W.boxValue α μ = μ ⬝ᵥ α - W.cost μ := hcap.trans hopt
  have hXmem := W.tauInf_mem hc hDpos hDconv hcost_conv α qb hqb
  have hYmem := W.tauInf_mem hc hDpos hDconv hcost_conv α μ hμ0
  have hXY : W.tauMinSet α qb ⊆ W.tauMinSet α μ := by
    intro τ hτ
    have hk := (W.mem_tauMinSet_iff_kkt hDpos hDconv hcost_conv α hqb
      hμD hμle hopt τ).mp hτ
    refine (W.mem_tauMinSet_iff_kkt hDpos hDconv hcost_conv α hμ0
      hμD le_rfl hoptμ τ).mpr ⟨hk.1, ?_⟩
    simp [TauSlack, tauPair]
  apply le_antisymm
  · intro i
    unfold tauInf tauSetInf
    refine le_iInf fun x => ?_
    exact iInf_le_of_le
      (⟨x.1, hXY x.2⟩ : W.tauMinSet α μ) le_rfl
  · intro i
    unfold tauInf tauSetInf
    refine le_iInf fun y => ?_
    let x := W.tauInf α qb
    have hmeetY : x ⊓ y.1 ∈ W.tauMinSet α μ :=
      (W.tauMinSet_pOrder hc hDpos hDconv hcost_conv α hμ0
        (fun _ => le_rfl) x (hXY hXmem) y.1 y.2).1
    have hky := (W.mem_tauMinSet_iff_kkt hDpos hDconv hcost_conv α hμ0
      hμD le_rfl hoptμ (x ⊓ y.1)).mp hmeetY
    have hkx := (W.mem_tauMinSet_iff_kkt hDpos hDconv hcost_conv α hqb
      hμD hμle hopt x).mp hXmem
    have hslack : TauSlack qb μ (x ⊓ y.1) := by
      change tauPair (qb - μ) (x ⊓ y.1) = 0
      apply le_antisymm
      · calc
          tauPair (qb - μ) (x ⊓ y.1) ≤ tauPair (qb - μ) x :=
            tauPair_mono_right (sub_nonneg.mpr hμle) inf_le_left
          _ = 0 := hkx.2
      · exact bot_le
    have hmeetX : x ⊓ y.1 ∈ W.tauMinSet α qb :=
      (W.mem_tauMinSet_iff_kkt hDpos hDconv hcost_conv α hqb
        hμD hμle hopt (x ⊓ y.1)).mpr ⟨hky.1, hslack⟩
    calc
      (⨅ z : W.tauMinSet α qb, z.1 i) ≤
          (⟨x ⊓ y.1, hmeetX⟩ : W.tauMinSet α qb).1 i := iInf_le _ _
      _ ≤ y.1 i := inf_le_right

theorem tauInf_capacity_eq_of_mem_rejectSet (hc : Exchangeable W.cFn)
    (hDpos : ∀ q ∈ W.D, 0 ≤ q) (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost)
    {α qb r : ι → ℝ} (hqb : 0 ≤ qb) (hr : r ∈ W.rejectSet α qb) :
    W.tauInf α (qb - r) = W.tauInf α qb := by
  obtain ⟨hr0, haccD, -⟩ := (W.mem_rejectSet_iff_acceptance hqb).mp hr
  apply W.tauInf_capacity_eq_of_opt hc hDpos hDconv hcost_conv α hqb haccD
  · intro i
    have hi : (0 : ℝ) ≤ r i := hr0 i
    change qb i - r i ≤ qb i
    linarith
  · exact W.boxValue_eq_of_mem_rejectSet hqb hr

end WelfareDual

namespace DASequences

variable {ι : Type*} [Fintype ι]

/-- The proposer's canonical exact waiting time in round `k`. -/
noncomputable def proposerTau (WG : WelfareDual ι) (s : DASequences ι)
    (α : ι → ℝ) (k : ℕ) : ι → ENNReal :=
  WG.tauInf α (s.A k)

/-- **Lemma 3, proposer half.** Canonical proposer waiting times are weakly
increasing along the decreasing availability sequence. -/
theorem monotone_proposerTau (WG : WelfareDual ι) (s : DASequences ι)
    (hcG : Exchangeable WG.cFn) (hDGpos : ∀ q ∈ WG.D, 0 ≤ q)
    (hDGconv : Convex ℝ WG.D) (hGcost_conv : ConvexOn ℝ WG.D WG.cost)
    (α : ι → ℝ) : Monotone (proposerTau WG s α) := by
  intro k l hkl
  exact WG.tauInf_anti_capacity hcG hDGpos hDGconv hGcost_conv α
    (s.nonneg_A l) (s.antitone_A hkl)

/-- The receiver's canonical exact waiting time in round `k`. -/
noncomputable def receiverTau (WH : WelfareDual ι) (s : DASequences ι)
    (γ : ι → ℝ) (k : ℕ) : ι → ENNReal :=
  WH.tauInf γ (s.P k)

/-- **Lemma 3, receiver half.** The cross-round proposal invariant and the
disposal rejection certificate make the receiver's least waiting times
weakly decreasing.  The hypothesis `hcH` is essential: it is the symmetric
submodularity assumption needed for Topkis on the receiver welfare. -/
theorem antitone_receiverTau (WH : WelfareDual ι) (s : DASequences ι)
    (hcH : Exchangeable WH.cFn) (hDHpos : ∀ q ∈ WH.D, 0 ≤ q)
    (hDHconv : Convex ℝ WH.D) (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    (γ : ι → ℝ) (hcross : ∀ k, s.T k ≤ s.P (k + 1))
    (hrejH : ∀ k, s.P k - s.T k ∈ WH.rejectSet γ (s.P k)) :
    Antitone (receiverTau WH s γ) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hPk0 : 0 ≤ s.P k := (s.nonneg_T k).trans (s.T_le_P k)
  have heq : WH.tauInf γ (s.T k) = WH.tauInf γ (s.P k) := by
    have h := WH.tauInf_capacity_eq_of_mem_rejectSet hcH hDHpos hDHconv
      hHcost_conv hPk0 (hrejH k)
    have he : s.P k - (s.P k - s.T k) = s.T k := by abel
    rw [he] at h
    exact h
  change WH.tauInf γ (s.P (k + 1)) ≤ WH.tauInf γ (s.P k)
  rw [← heq]
  exact WH.tauInf_anti_capacity hcH hDHpos hDHconv hHcost_conv γ
    (s.nonneg_T k) (hcross k)

theorem receiverTau_slack (WH : WelfareDual ι) (s : DASequences ι)
    (hcH : Exchangeable WH.cFn) (hDHpos : ∀ q ∈ WH.D, 0 ≤ q)
    (hDHconv : Convex ℝ WH.D) (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    (γ : ι → ℝ) (hrejH : ∀ k, s.P k - s.T k ∈ WH.rejectSet γ (s.P k))
    (k : ℕ) : WelfareDual.TauSlack (s.P k) (s.T k)
      (receiverTau WH s γ k) := by
  have hPk0 : 0 ≤ s.P k := (s.nonneg_T k).trans (s.T_le_P k)
  obtain ⟨-, haccD, -⟩ :=
    (WH.mem_rejectSet_iff_acceptance hPk0).mp (hrejH k)
  have hTD : s.T k ∈ WH.D := by
    have he : s.P k - (s.P k - s.T k) = s.T k := by abel
    rwa [he] at haccD
  have hopt : WH.boxValue γ (s.P k) =
      s.T k ⬝ᵥ γ - WH.cost (s.T k) := by
    have h := WH.boxValue_eq_of_mem_rejectSet hPk0 (hrejH k)
    have he : s.P k - (s.P k - s.T k) = s.T k := by abel
    rwa [he] at h
  have hmem : receiverTau WH s γ k ∈ WH.tauMinSet γ (s.P k) :=
    WH.tauInf_mem hcH hDHpos hDHconv hHcost_conv γ (s.P k) hPk0
  exact (WH.mem_tauMinSet_iff_kkt hDHpos hDHconv hHcost_conv γ hPk0
    hTD (s.T_le_P k) hopt _).mp hmem |>.2

/-- **Lemma 3 (exact compactified waiting-time monotonicity).** Algorithm 1
admits canonical attained least waiting times: proposer waits increase and
receiver waits decrease.  The symmetric exchangeability hypothesis `hcH` is
made explicit; it was absent from the earlier ε-equilibrium API. -/
theorem lemma3_exact (WG WH : WelfareDual ι) (α γ : ι → ℝ)
    (hcG : Exchangeable WG.cFn) (hcH : Exchangeable WH.cFn)
    (hDGpos : ∀ q ∈ WG.D, 0 ≤ q) (hDHpos : ∀ q ∈ WH.D, 0 ≤ q)
    (hDGconv : Convex ℝ WG.D) (hDHconv : Convex ℝ WH.D)
    (hGcost_conv : ConvexOn ℝ WG.D WG.cost)
    (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) :
    ∃ s : DASequences ι, s.A 0 = A0 ∧
      (∀ k, s.A k - s.P k ∈ WG.rejectSet α (s.A k)) ∧
      (∀ k, s.P k - s.T k ∈ WH.rejectSet γ (s.P k)) ∧
      Monotone (proposerTau WG s α) ∧ Antitone (receiverTau WH s γ) := by
  obtain ⟨s, hs0, hrejG, hrejH, hcross⟩ :=
    algorithm_wellDefined (WG := WG) (WH := WH) (α := α) (γ := γ)
      hcG hDGpos hDHpos hA0
  refine ⟨s, hs0, hrejG, hrejH,
    monotone_proposerTau WG s hcG hDGpos hDGconv hGcost_conv α, ?_⟩
  exact antitone_receiverTau WH s hcH hDHpos hDHconv hHcost_conv γ hcross hrejH

/-- Coordinatewise monotone limit of proposer waiting times. -/
noncomputable def proposerTauLimit (WG : WelfareDual ι) (s : DASequences ι)
    (α : ι → ℝ) : ι → ENNReal := fun i => ⨆ k, proposerTau WG s α k i

/-- Coordinatewise monotone limit of receiver waiting times. -/
noncomputable def receiverTauLimit (WH : WelfareDual ι) (s : DASequences ι)
    (γ : ι → ℝ) : ι → ENNReal := fun i => ⨅ k, receiverTau WH s γ k i

theorem tendsto_proposerTau (WG : WelfareDual ι) (s : DASequences ι)
    (α : ι → ℝ) (hmono : Monotone (proposerTau WG s α)) :
    Tendsto (proposerTau WG s α) atTop (𝓝 (proposerTauLimit WG s α)) := by
  rw [tendsto_pi_nhds]
  intro i
  exact tendsto_atTop_iSup fun k l hkl => hmono hkl i

theorem tendsto_receiverTau (WH : WelfareDual ι) (s : DASequences ι)
    (γ : ι → ℝ) (hanti : Antitone (receiverTau WH s γ)) :
    Tendsto (receiverTau WH s γ) atTop (𝓝 (receiverTauLimit WH s γ)) := by
  rw [tendsto_pi_nhds]
  intro i
  exact tendsto_atTop_iInf fun k l hkl => hanti hkl i

end DASequences

/-! ## Theorem 3: exact compactified equilibrium at the algorithmic limit -/

variable {ι : Type*} [Fintype ι] {WG WH : WelfareDual ι} {α γ : ι → ℝ}

/-- Exact generalized-equilibrium KKT data at the limit found by Algorithm 1.

This closes the exact-attainment part of Theorem 3.  Identifying these
canonical multipliers with the monotone limits of the round-by-round
multipliers, and imposing the paper's final coordinatewise `min = 0`
normalization, are separate statements: the latter needs the side-specific
capacity bounds and initialization that are not fields of `WelfareDual`. -/
theorem theorem3_exact_compact (hcG : Exchangeable WG.cFn)
    (hcH : Exchangeable WH.cFn)
    (hDGpos : ∀ q ∈ WG.D, 0 ≤ q) (hDHpos : ∀ q ∈ WH.D, 0 ≤ q)
    (hDGconv : Convex ℝ WG.D) (hDHconv : Convex ℝ WH.D)
    (hGcost_conv : ConvexOn ℝ WG.D WG.cost)
    (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) :
    ∃ (s : DASequences ι) (μ : ι → ℝ)
      (τα τγ : ι → ENNReal),
      s.A 0 = A0 ∧ 0 ≤ μ ∧ μ ≤ s.Ainf ∧
      s.Ainf - μ ∈ WG.rejectSet α s.Ainf ∧
      0 ∈ WH.rejectSet γ μ ∧
      τα = WG.tauInf α s.Ainf ∧ τγ = WH.tauInf γ μ ∧
      WG.ExtTight α μ τα ∧ WelfareDual.TauSlack s.Ainf μ τα ∧
      WH.ExtTight γ μ τγ ∧ WelfareDual.TauSlack μ μ τγ := by
  obtain ⟨s, μ, φ, hs0, hφ, hPt, hTt, hμ0, hμA, hG, hH⟩ :=
    theorem3_limit (WG := WG) (WH := WH) (α := α) (γ := γ)
      hcG hDGpos hDHpos hDHconv hA0
  have hμDG : μ ∈ WG.D := by
    obtain ⟨-, hD, -⟩ :=
      (WG.mem_rejectSet_iff_acceptance s.nonneg_Ainf).mp hG
    rwa [sub_sub_cancel] at hD
  have hoptG : WG.boxValue α s.Ainf = μ ⬝ᵥ α - WG.cost μ := by
    have h := WG.boxValue_eq_of_mem_rejectSet s.nonneg_Ainf hG
    rwa [sub_sub_cancel] at h
  have hταmem := WG.tauInf_mem hcG hDGpos hDGconv hGcost_conv
    α s.Ainf s.nonneg_Ainf
  have hkG := (WG.mem_tauMinSet_iff_kkt hDGpos hDGconv hGcost_conv α
    s.nonneg_Ainf hμDG hμA hoptG (WG.tauInf α s.Ainf)).mp hταmem
  have hμDH : μ ∈ WH.D := by
    obtain ⟨-, hD, -⟩ := (WH.mem_rejectSet_iff_acceptance hμ0).mp hH
    rwa [sub_zero] at hD
  have hoptH : WH.boxValue γ μ = μ ⬝ᵥ γ - WH.cost μ := by
    have h := WH.boxValue_eq_of_mem_rejectSet hμ0 hH
    rwa [sub_zero] at h
  have hτγmem := WH.tauInf_mem hcH hDHpos hDHconv hHcost_conv γ μ hμ0
  have hkH := (WH.mem_tauMinSet_iff_kkt hDHpos hDHconv hHcost_conv γ
    hμ0 hμDH le_rfl hoptH (WH.tauInf γ μ)).mp hτγmem
  exact ⟨s, μ, WG.tauInf α s.Ainf, WH.tauInf γ μ,
    hs0, hμ0, hμA, hG, hH, rfl, rfl, hkG.1, hkG.2, hkH.1, hkH.2⟩

/-- **Theorem 3 with the waiting times obtained as the monotone limits of
the round-by-round least multipliers.** This is the closed-graph step left
open in `theorem3_exact_compact`. -/
theorem theorem3_exact_limits (hcG : Exchangeable WG.cFn)
    (hcH : Exchangeable WH.cFn)
    (hDGpos : ∀ q ∈ WG.D, 0 ≤ q) (hDHpos : ∀ q ∈ WH.D, 0 ≤ q)
    (hDGconv : Convex ℝ WG.D) (hDHconv : Convex ℝ WH.D)
    (hGcost_conv : ConvexOn ℝ WG.D WG.cost)
    (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) :
    ∃ (s : DASequences ι) (μ : ι → ℝ) (φ : ℕ → ℕ)
      (τα τγ : ι → ENNReal),
      s.A 0 = A0 ∧ StrictMono φ ∧
      Tendsto (fun k => s.P (φ k)) atTop (𝓝 μ) ∧
      Tendsto (fun k => s.T (φ k)) atTop (𝓝 μ) ∧
      0 ≤ μ ∧ μ ≤ s.Ainf ∧
      s.Ainf - μ ∈ WG.rejectSet α s.Ainf ∧
      0 ∈ WH.rejectSet γ μ ∧
      (∀ k, s.A k - s.P k ∈ WG.rejectSet α (s.A k)) ∧
      (∀ k, s.P k - s.T k ∈ WH.rejectSet γ (s.P k)) ∧
      (∀ k, s.T k ≤ s.P (k + 1)) ∧
      τα = DASequences.proposerTauLimit WG s α ∧
      τγ = DASequences.receiverTauLimit WH s γ ∧
      Tendsto (DASequences.proposerTau WG s α) atTop (𝓝 τα) ∧
      Tendsto (DASequences.receiverTau WH s γ) atTop (𝓝 τγ) ∧
      τα ∈ WG.tauMinSet α s.Ainf ∧ τγ ∈ WH.tauMinSet γ μ ∧
      WG.ExtTight α μ τα ∧ WelfareDual.TauSlack s.Ainf μ τα ∧
      WH.ExtTight γ μ τγ ∧ WelfareDual.TauSlack μ μ τγ := by
  obtain ⟨s, hs0, hrejG, hrejH, hcross⟩ :=
    algorithm_wellDefined (WG := WG) (WH := WH) (α := α) (γ := γ)
      hcG hDGpos hDHpos hA0
  obtain ⟨μ, hμbox, φ, hφ, hPt, hTt⟩ := s.exists_subseq_tendsto
  have hAt : Tendsto (fun k => s.A (φ k)) atTop (𝓝 s.Ainf) :=
    s.tendsto_A.comp hφ.tendsto_atTop
  have hμA : μ ≤ s.Ainf := by
    intro i
    refine le_of_tendsto_of_tendsto' (tendsto_pi_nhds.mp hPt i)
      (tendsto_pi_nhds.mp hAt i) fun k => s.P_le_A (φ k) i
  have hG : s.Ainf - μ ∈ WG.rejectSet α s.Ainf := by
    refine WG.rejectSet_limit_antitone α s.nonneg_Ainf
      (fun k => s.Ainf_le (φ k)) hAt (hAt.sub hPt) ?_
    exact fun k => hrejG (φ k)
  have hH : 0 ∈ WH.rejectSet γ μ := by
    refine WH.rejectSet_fixedPoint_of_tendsto hDHconv hDHpos γ
      (fun k => (s.nonneg_T (φ k)).trans (s.T_le_P (φ k)))
      (fun k => hrejH (φ k)) hPt hTt
  have hmono := DASequences.monotone_proposerTau WG s hcG hDGpos
    hDGconv hGcost_conv α
  have hanti := DASequences.antitone_receiverTau WH s hcH hDHpos
    hDHconv hHcost_conv γ hcross hrejH
  let τα := DASequences.proposerTauLimit WG s α
  let τγ := DASequences.receiverTauLimit WH s γ
  have hταt : Tendsto (DASequences.proposerTau WG s α) atTop (𝓝 τα) :=
    DASequences.tendsto_proposerTau WG s α hmono
  have hτγt : Tendsto (DASequences.receiverTau WH s γ) atTop (𝓝 τγ) :=
    DASequences.tendsto_receiverTau WH s γ hanti
  have hταmem : τα ∈ WG.tauMinSet α s.Ainf := by
    apply WG.tauMinSet_limit hDGpos hDGconv hGcost_conv α
      (fun k => s.nonneg_A k) s.nonneg_Ainf s.tendsto_A hταt
    intro k
    exact WG.tauInf_mem hcG hDGpos hDGconv hGcost_conv α (s.A k)
      (s.nonneg_A k)
  have hτγmem : τγ ∈ WH.tauMinSet γ μ := by
    apply WH.tauMinSet_limit hDHpos hDHconv hHcost_conv γ
      (fun k => (s.nonneg_T (φ k)).trans (s.T_le_P (φ k))) hμbox.1 hPt
      (hτγt.comp hφ.tendsto_atTop)
    intro k
    exact WH.tauInf_mem hcH hDHpos hDHconv hHcost_conv γ (s.P (φ k))
      ((s.nonneg_T (φ k)).trans (s.T_le_P (φ k)))
  have hμDG : μ ∈ WG.D := by
    obtain ⟨-, hD, -⟩ :=
      (WG.mem_rejectSet_iff_acceptance s.nonneg_Ainf).mp hG
    rwa [sub_sub_cancel] at hD
  have hoptG : WG.boxValue α s.Ainf = μ ⬝ᵥ α - WG.cost μ := by
    have h := WG.boxValue_eq_of_mem_rejectSet s.nonneg_Ainf hG
    rwa [sub_sub_cancel] at h
  have hkG := (WG.mem_tauMinSet_iff_kkt hDGpos hDGconv hGcost_conv α
    s.nonneg_Ainf hμDG hμA hoptG τα).mp hταmem
  have hμDH : μ ∈ WH.D := by
    obtain ⟨-, hD, -⟩ := (WH.mem_rejectSet_iff_acceptance hμbox.1).mp hH
    rwa [sub_zero] at hD
  have hoptH : WH.boxValue γ μ = μ ⬝ᵥ γ - WH.cost μ := by
    have h := WH.boxValue_eq_of_mem_rejectSet hμbox.1 hH
    rwa [sub_zero] at h
  have hkH := (WH.mem_tauMinSet_iff_kkt hDHpos hDHconv hHcost_conv γ
    hμbox.1 hμDH le_rfl hoptH τγ).mp hτγmem
  exact ⟨s, μ, φ, τα, τγ, hs0, hφ, hPt, hTt, hμbox.1, hμA,
    hG, hH, hrejG, hrejH, hcross, rfl, rfl, hταt, hτγt, hταmem, hτγmem,
    hkG.1, hkG.2, hkH.1, hkH.2⟩

/-- **Theorem 3, full corrected exact form.** With the side-specific domain
bounds and the paper's intended initialization made explicit, the monotone
waiting-time limits can be normalized on saturated coordinates without
losing exact KKT tightness, and their coordinatewise minimum is zero. -/
theorem theorem3_exact_equilibrium (hcG : Exchangeable WG.cFn)
    (hcH : Exchangeable WH.cFn)
    (hDGpos : ∀ q ∈ WG.D, 0 ≤ q) (hDHpos : ∀ q ∈ WH.D, 0 ≤ q)
    (hDGconv : Convex ℝ WG.D) (hDHconv : Convex ℝ WH.D)
    (hGcost_conv : ConvexOn ℝ WG.D WG.cost)
    (hHcost_conv : ConvexOn ℝ WH.D WH.cost)
    {nG nH : ι → ℝ} (hnG0 : 0 ≤ nG) (hnH0 : 0 ≤ nH)
    (hDGbound : ∀ ν ∈ WG.D, ν ≤ nG)
    (hDHbound : ∀ ν ∈ WH.D, ν ≤ nH) :
    ∃ (s : DASequences ι) (μ : ι → ℝ) (φ : ℕ → ℕ)
      (rawP rawT τα τγ : ι → ENNReal),
      s.A 0 = nG ⊓ nH ∧ StrictMono φ ∧
      Tendsto (fun k => s.P (φ k)) atTop (𝓝 μ) ∧
      Tendsto (fun k => s.T (φ k)) atTop (𝓝 μ) ∧
      0 ≤ μ ∧ μ ≤ s.Ainf ∧
      s.Ainf - μ ∈ WG.rejectSet α s.Ainf ∧
      0 ∈ WH.rejectSet γ μ ∧
      rawP = DASequences.proposerTauLimit WG s α ∧
      rawT = DASequences.receiverTauLimit WH s γ ∧
      Tendsto (DASequences.proposerTau WG s α) atTop (𝓝 rawP) ∧
      Tendsto (DASequences.receiverTau WH s γ) atTop (𝓝 rawT) ∧
      τα = WelfareDual.normalizeTau nG μ rawP ∧
      τγ = WelfareDual.normalizeTau nH μ rawT ∧
      τα ∈ WG.tauMinSet α s.Ainf ∧ τγ ∈ WH.tauMinSet γ μ ∧
      WG.ExtTight α μ τα ∧ WelfareDual.TauSlack s.Ainf μ τα ∧
      WH.ExtTight γ μ τγ ∧ WelfareDual.TauSlack μ μ τγ ∧
      ∀ i, τα i ⊓ τγ i = 0 := by
  have hA0 : 0 ≤ nG ⊓ nH := fun i =>
    le_inf (hnG0 i) (hnH0 i)
  obtain ⟨s, μ, φ, rawP, rawT, hs0, hφ, hPt, hTt, hμ0, hμA,
    hG, hH, hrejG, hrejH, hcross, hrawPdef, hrawTdef, hrawPt, hrawTt,
    hrawPmem, hrawTmem, htightP, hslackP, htightT, hslackT⟩ :=
    theorem3_exact_limits (WG := WG) (WH := WH) (α := α) (γ := γ)
      hcG hcH hDGpos hDHpos hDGconv hDHconv hGcost_conv hHcost_conv hA0
  have hμDG : μ ∈ WG.D := by
    obtain ⟨-, hD, -⟩ :=
      (WG.mem_rejectSet_iff_acceptance s.nonneg_Ainf).mp hG
    rwa [sub_sub_cancel] at hD
  have hμDH : μ ∈ WH.D := by
    obtain ⟨-, hD, -⟩ := (WH.mem_rejectSet_iff_acceptance hμ0).mp hH
    rwa [sub_zero] at hD
  let τα := WelfareDual.normalizeTau nG μ rawP
  let τγ := WelfareDual.normalizeTau nH μ rawT
  have htightα : WG.ExtTight α μ τα :=
    WG.extTight_normalize hDGpos hμDG hDGbound htightP
  have hslackα : WelfareDual.TauSlack s.Ainf μ τα :=
    WelfareDual.tauSlack_normalize hμA hslackP
  have htightγ : WH.ExtTight γ μ τγ :=
    WH.extTight_normalize hDHpos hμDH hDHbound htightT
  have hslackγ : WelfareDual.TauSlack μ μ τγ :=
    WelfareDual.tauSlack_normalize le_rfl hslackT
  have hταmem : τα ∈ WG.tauMinSet α s.Ainf :=
    (WG.tauObjective_eq_of_kkt hDGpos α s.nonneg_Ainf hμDG hμA
      htightα hslackα).2
  have hτγmem : τγ ∈ WH.tauMinSet γ μ :=
    (WH.tauObjective_eq_of_kkt hDHpos γ hμ0 hμDH le_rfl
      htightγ hslackγ).2
  have hanti := DASequences.antitone_receiverTau WH s hcH hDHpos
    hDHconv hHcost_conv γ hcross hrejH
  have hminzero : ∀ i, τα i ⊓ τγ i = 0 := by
    intro i
    by_cases hα0 : τα i = 0
    · simp [hα0]
    by_cases hγ0 : τγ i = 0
    · simp [hγ0]
    exfalso
    have hμneG : μ i ≠ nG i := by
      intro h
      apply hα0
      simp [τα, WelfareDual.normalizeTau, h]
    have hμneH : μ i ≠ nH i := by
      intro h
      apply hγ0
      simp [τγ, WelfareDual.normalizeTau, h]
    have hrawP0 : rawP i ≠ 0 := by
      intro h
      apply hα0
      simp [τα, WelfareDual.normalizeTau, h]
    have hrawT0 : rawT i ≠ 0 := by
      intro h
      apply hγ0
      simp [τγ, WelfareDual.normalizeTau, h]
    have hμltG : μ i < nG i := lt_of_le_of_ne (hDGbound μ hμDG i) hμneG
    have hμltH : μ i < nH i := lt_of_le_of_ne (hDHbound μ hμDH i) hμneH
    have hseqT0 (k : ℕ) : DASequences.receiverTau WH s γ k i ≠ 0 := by
      intro hk0
      apply hrawT0
      apply le_antisymm
      · rw [hrawTdef]
        exact iInf_le_of_le k (by rw [hk0])
      · exact bot_le
    have hPTeq (k : ℕ) : s.P k i = s.T k i := by
      apply le_antisymm
      · by_contra hne
        have hlt : s.T k i < s.P k i := lt_of_not_ge hne
        have hz := WelfareDual.tau_eq_zero_of_slack_of_lt
          (DASequences.receiverTau_slack WH s hcH hDHpos hDHconv
            hHcost_conv γ hrejH k) hlt
        exact hseqT0 k hz
      · exact s.T_le_P k i
    have hAconst : ∀ k, s.A k i = (nG ⊓ nH) i := by
      intro k
      induction k with
      | zero => exact congrFun hs0 i
      | succ k ih =>
          rw [s.update k]
          change s.A k i - (s.P k i - s.T k i) = (nG ⊓ nH) i
          rw [hPTeq k, sub_self, sub_zero, ih]
    have hAinf : s.Ainf i = (nG ⊓ nH) i := by
      unfold DASequences.Ainf
      simp_rw [hAconst]
      simp
    have hμAeq : μ i = s.Ainf i := by
      apply le_antisymm (hμA i)
      apply le_of_not_gt
      intro hlt
      exact hrawP0 (WelfareDual.tau_eq_zero_of_slack_of_lt hslackP hlt)
    have hμinit : μ i = (nG ⊓ nH) i := hμAeq.trans hAinf
    rcases le_total (nG i) (nH i) with hGH | hHG
    · have hi : (nG ⊓ nH) i = nG i := by
        simp only [Pi.inf_apply, inf_eq_left.mpr hGH]
      rw [hi] at hμinit
      exact hμneG hμinit
    · have hi : (nG ⊓ nH) i = nH i := by
        simp only [Pi.inf_apply, inf_eq_right.mpr hHG]
      rw [hi] at hμinit
      exact hμneH hμinit
  exact ⟨s, μ, φ, rawP, rawT, τα, τγ, hs0, hφ, hPt, hTt, hμ0, hμA,
    hG, hH, hrawPdef, hrawTdef, hrawPt, hrawTt, rfl, rfl, hταmem, hτγmem, htightα, hslackα,
    htightγ, hslackγ, hminzero⟩

end GHS
