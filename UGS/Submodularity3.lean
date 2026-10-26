import UGS.Submodular
import UGS.Correspondence
import UGS.FiniteConvex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# GSV Theorem 3 (i)⟺(ii): submodular `c*` ⟺ `∂c*` is UGS  (Phase 3, WIP)

Formalizes the convex-analysis half of GSV Theorem 3 using the standalone,
finite-dimensional convex-analysis layer in `UGS.FiniteConvex`. See
`THEOREM3-PLAN.md` for the full pinned proof and lemma map
(L1 char-subdiff = Thm 23.4 / L2 tympani = Thm 13.1 / L3 diffcstartilde /
L4 huddle `Submodular.lean` / L5 diff-char-submod = ours).

Both directions are fully proved (no `sorry`). Forward `(i)⟹(ii)`: the meet/join
directional-derivative inequalities plus the two Hahn-Banach selections
(`exists_subgrad_ge` and its dual `exists_subgrad_le`). Backward `(ii)⟹(i)`: `DD` is
derived from `IsUGS` via attained subgradients, then L5-backward (`submodular_of_dderiv`)
closes it by a Dini-derivative fencing argument using Mathlib's convex right derivative.
-/

open scoped Pointwise
open Matrix Correspondence

namespace Correspondence

variable {n : ℕ}

/-- The **mix** of `q, q'` along the price comparison: `q` where `p ≤ p'`,
`q'` where `p > p'`. GSV's `q 1_{Z≤} + q' 1_{Z>}`. -/
noncomputable def mix (p p' q q' : Fin n → ℝ) : Fin n → ℝ :=
  fun z => if p z ≤ p' z then q z else q' z

/-- **Mix identity** (pure algebra): `⟨mix, b⟩ = ⟨q, b^≤⟩ + ⟨q', b^>⟩`, where
`b^≤ = borderLe p p' b`, `b^> = borderGt p p' b`. This is the algebraic hinge of
both directions of Theorem 3. -/
theorem dotProduct_mix (p p' q q' b : Fin n → ℝ) :
    (mix p p' q q') ⬝ᵥ b
      = q ⬝ᵥ borderLe p p' b + q' ⬝ᵥ borderGt p p' b := by
  simp only [dotProduct]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : p z ≤ p' z <;> simp [mix, borderLe, borderGt, h]

/-! ## L5 foundations: border scaling and real difference quotients -/

/-- `(t•b)^≤ = t•(b^≤)`. -/
theorem borderLe_smul (p p' b : Fin n → ℝ) (t : ℝ) :
    borderLe p p' (t • b) = t • borderLe p p' b := by
  funext z
  by_cases h : p z ≤ p' z <;> simp [borderLe, Pi.smul_apply, smul_eq_mul, h]

/-- `(t•b)^> = t•(b^>)`. -/
theorem borderGt_smul (p p' b : Fin n → ℝ) (t : ℝ) :
    borderGt p p' (t • b) = t • borderGt p p' b := by
  funext z
  by_cases h : p z ≤ p' z <;> simp [borderGt, Pi.smul_apply, smul_eq_mul, h]

/-- The forward directional difference quotient. -/
noncomputable def dirQuot (f : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) (t : ℝ) : ℝ :=
  (f (x + t • y) - f x) / t

/-- The huddle inequality at scaled step `t•b`, read as difference quotients: for a
submodular `f`, `t > 0`, and the small-step precondition, the `p`-quotient along `b^≤`
plus the `p'`-quotient along `b^>` is at most the `(p⊓p')`-quotient along `b`. -/
theorem dq_huddle (f : (Fin n → ℝ) → ℝ) (hsub : Submodular f) (p p' b : Fin n → ℝ)
    (hb : 0 ≤ b) {t : ℝ} (ht : 0 < t) (hpre : ∀ z, p' z < p z → t * b z ≤ p z - p' z) :
    dirQuot f p (borderLe p p' b) t + dirQuot f p' (borderGt p p' b) t
      ≤ dirQuot f (p ⊓ p') b t := by
  have hH := (submodular_iff_huddle f).mp hsub p p' (t • b) (smul_nonneg ht.le hb)
    (by intro z hz; simpa [Pi.smul_apply, smul_eq_mul] using hpre z hz)
  rw [borderLe_smul, borderGt_smul] at hH
  have key : (f (p + t • borderLe p p' b) - f p)
      + (f (p' + t • borderGt p p' b) - f p')
      ≤ f (p ⊓ p' + t • b) - f (p ⊓ p') := by linarith [hH]
  simpa only [dirQuot, add_div] using div_le_div_of_nonneg_right key ht.le

/-- **Join huddle** (join analog of GSV Lemma 6, derived directly from submodularity by two
applications at `(p', p⊔p'+c)` and `(p⊔p'+b^>, p)`). For `c ≤ 0` with `p'-p ≤ c` on `{p'<p}`:
`f(p' + c^≤) + f(p + c^>) + f(p⊔p') ≤ f p' + f p + f(p⊔p' + c)`. -/
theorem huddle_join (f : (Fin n → ℝ) → ℝ) (hsub : Submodular f) (p p' c : Fin n → ℝ)
    (hc : c ≤ 0) (hcond : ∀ z, p' z < p z → p' z - p z ≤ c z) :
    f (p' + borderLe p p' c) + f (p + borderGt p p' c) + f (p ⊔ p')
      ≤ f p' + f p + f (p ⊔ p' + c) := by
  have hcz : ∀ z, c z ≤ 0 := fun z => hc z
  have L1 : p' ⊓ (p ⊔ p' + c) = p' + borderLe p p' c := by
    funext z
    simp only [Pi.inf_apply, Pi.sup_apply, Pi.add_apply, borderLe]
    by_cases h : p z ≤ p' z
    · have hle : p' z + c z ≤ p' z := by linarith [hcz z]
      simp only [sup_of_le_right h, if_pos h]; rw [inf_of_le_right hle]
    · have hlt : p' z < p z := not_le.mp h
      have hle : p' z ≤ p z + c z := by linarith [hcond z hlt]
      simp only [sup_of_le_left hlt.le, if_neg h, add_zero]; rw [inf_of_le_left hle]
  have L2 : p' ⊔ (p ⊔ p' + c) = p ⊔ p' + borderGt p p' c := by
    funext z
    simp only [Pi.sup_apply, Pi.add_apply, borderGt]
    by_cases h : p z ≤ p' z
    · have hle : p' z + c z ≤ p' z := by linarith [hcz z]
      simp only [sup_of_le_right h, if_pos h, add_zero]; rw [sup_of_le_left hle]
    · have hlt : p' z < p z := not_le.mp h
      have hle : p' z ≤ p z + c z := by linarith [hcond z hlt]
      simp only [sup_of_le_left hlt.le, if_neg h]; rw [sup_of_le_right hle]
  have L3 : (p ⊔ p' + borderGt p p' c) ⊓ p = p + borderGt p p' c := by
    funext z
    simp only [Pi.inf_apply, Pi.sup_apply, Pi.add_apply, borderGt]
    by_cases h : p z ≤ p' z
    · simp only [sup_of_le_right h, if_pos h, add_zero]; rw [inf_of_le_right h]
    · have hlt : p' z < p z := not_le.mp h
      have hle : p z + c z ≤ p z := by linarith [hcz z]
      simp only [sup_of_le_left hlt.le, if_neg h]; rw [inf_of_le_left hle]
  have L4 : (p ⊔ p' + borderGt p p' c) ⊔ p = p ⊔ p' := by
    funext z
    simp only [Pi.sup_apply, Pi.add_apply, borderGt]
    by_cases h : p z ≤ p' z
    · simp only [sup_of_le_right h, if_pos h, add_zero]; rw [sup_of_le_left h]
    · have hlt : p' z < p z := not_le.mp h
      have hle : p z + c z ≤ p z := by linarith [hcz z]
      simp only [sup_of_le_left hlt.le, if_neg h]; rw [sup_of_le_right hle]
  have S1 := hsub p' (p ⊔ p' + c)
  rw [L1, L2] at S1
  have S2 := hsub (p ⊔ p' + borderGt p p' c) p
  rw [L3, L4] at S2
  linarith [S1, S2]

/-- The huddle precondition `b^> ≤ (p-p')⁺` holds for the scaled step `t•b` once
`t` is small enough: there is `ε > 0` with `t·b_z ≤ p_z - p'_z` on `{p' < p}` for all
`0 < t ≤ ε`. This lets the directional-derivative (`t → 0`) limit see the huddle. -/
theorem exists_small_step (p p' b : Fin n → ℝ) (hb : 0 ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t ≤ ε →
      ∀ z, p' z < p z → t * b z ≤ p z - p' z := by
  classical
  by_cases hS : (Finset.univ.filter (fun z => p' z < p z)).Nonempty
  · refine ⟨(Finset.univ.filter (fun z => p' z < p z)).inf' hS
        (fun z => (p z - p' z) / (b z + 1)), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro z hz
      have h1 : p' z < p z := (Finset.mem_filter.mp hz).2
      have h2 : (0:ℝ) < b z + 1 := by have hbz : (0:ℝ) ≤ b z := hb z; linarith
      exact div_pos (by linarith) h2
    · intro t ht htε z hz
      have hmem : z ∈ Finset.univ.filter (fun z => p' z < p z) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩
      have hle : (Finset.univ.filter (fun z => p' z < p z)).inf'
          hS (fun z => (p z - p' z) / (b z + 1)) ≤ (p z - p' z) / (b z + 1) :=
        Finset.inf'_le _ hmem
      have hb1 : (0:ℝ) < b z + 1 := by have hbz : (0:ℝ) ≤ b z := hb z; linarith
      have htz : t ≤ (p z - p' z) / (b z + 1) := le_trans htε hle
      have hstep : t * (b z + 1) ≤ p z - p' z := by
        have hmul := mul_le_mul_of_nonneg_right htz hb1.le
        calc t * (b z + 1) ≤ (p z - p' z) / (b z + 1) * (b z + 1) := hmul
          _ = p z - p' z := by field_simp
      have hbz : t * b z ≤ t * (b z + 1) := mul_le_mul_of_nonneg_left (by linarith) ht.le
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro t ht htε z hz
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩)
      (by rw [Finset.not_nonempty_iff_eq_empty] at hS; rw [hS]; exact Finset.notMem_empty z)

/-- **L5, forward direction (GSV Lemma `diff-char-submod`, ⟹).** For a submodular
finite convex `f` and `b ≥ 0`,
`f'(p; b^≤) + f'(p'; b^>) ≤ f'(p⊓p'; b)`.
Proof: at each small step `t`, `dq_huddle` gives the quotient inequality; the directional
derivative is the `sInf` of positive difference quotients, so bounding it below by
`f'(p;b^≤)+f'(p';b^>)` reduces (via `le_sInf`/`sInf_le` + monotonicity) to that step
inequality. -/
theorem dderiv_of_submodular (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hsub : Submodular f) (p p' b : Fin n → ℝ) (hb : 0 ≤ b) :
    dderiv f p (borderLe p p' b) + dderiv f p' (borderGt p p' b)
      ≤ dderiv f (p ⊓ p') b := by
  obtain ⟨ε, hε, hεpre⟩ := exists_small_step p p' b hb
  have hP := tendsto_slope_dderiv f hconv p (borderLe p p' b)
  have hP' := tendsto_slope_dderiv f hconv p' (borderGt p p' b)
  have hM := tendsto_slope_dderiv f hconv (p ⊓ p') b
  apply le_of_tendsto_of_tendsto (hP.add hP') hM
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with t ht htε
  have hhud := dq_huddle f hsub p p' b hb ht
    (fun z hz => hεpre t ht htε.le z hz)
  simpa [dirQuot, slope_def_field] using hhud

/-- **The mix satisfies the directional inequality** (the heart of Theorem 3's direct
implication): for a submodular `f`, subgradients `q ∈ ∂f(p)`, `q' ∈ ∂f(p')`, and `b ≥ 0`,
`⟨mix q q', b⟩ ≤ f'(p⊓p'; b)`. Combines `dotProduct_mix`, `subgrad_le_dderiv` (L1), and
`dderiv_of_submodular` (L5, forward). -/
theorem mix_dderiv_le (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hsub : Submodular f) {p p' q q' : Fin n → ℝ}
    (hq : SubgradVec f p q) (hq' : SubgradVec f p' q') (b : Fin n → ℝ) (hb : 0 ≤ b) :
    (mix p p' q q') ⬝ᵥ b ≤ dderiv f (p ⊓ p') b := by
  rw [dotProduct_mix]
  calc q ⬝ᵥ borderLe p p' b + q' ⬝ᵥ borderGt p p' b
      ≤ dderiv f p (borderLe p p' b) + dderiv f p' (borderGt p p' b) :=
        add_le_add (subgrad_le_dderiv f hconv hq _) (subgrad_le_dderiv f hconv hq' _)
    _ ≤ dderiv f (p ⊓ p') b := dderiv_of_submodular f hconv hsub p p' b hb

/-- Join difference-quotient inequality (from `huddle_join` at scaled step `t•b`, `b ≤ 0`). -/
theorem dq_huddle_join (f : (Fin n → ℝ) → ℝ) (hsub : Submodular f) (p p' b : Fin n → ℝ)
    (hb : b ≤ 0) {t : ℝ} (ht : 0 < t) (hpre : ∀ z, p' z < p z → p' z - p z ≤ t * b z) :
    dirQuot f p' (borderLe p p' b) t + dirQuot f p (borderGt p p' b) t
      ≤ dirQuot f (p ⊔ p') b t := by
  have htb : (t • b) ≤ 0 := by
    rw [Pi.le_def]; intro z
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact mul_nonpos_iff.mpr (Or.inl ⟨ht.le, hb z⟩)
  have hH := huddle_join f hsub p p' (t • b) htb
    (by intro z hz; simpa [Pi.smul_apply, smul_eq_mul] using hpre z hz)
  rw [borderLe_smul, borderGt_smul] at hH
  have key : (f (p' + t • borderLe p p' b) - f p')
      + (f (p + t • borderGt p p' b) - f p)
      ≤ f (p ⊔ p' + t • b) - f (p ⊔ p') := by linarith [hH]
  simpa only [dirQuot, add_div] using div_le_div_of_nonneg_right key ht.le

/-- **Join L5** (join analog of `dderiv_of_submodular`, `b ≤ 0`):
`f'(p'; b^≤) + f'(p; b^>) ≤ f'(p⊔p'; b)`. The small-step precondition is `exists_small_step`
applied to `-b`. -/
theorem dderiv_of_submodular_join (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hsub : Submodular f) (p p' b : Fin n → ℝ) (hb : b ≤ 0) :
    dderiv f p' (borderLe p p' b) + dderiv f p (borderGt p p' b)
      ≤ dderiv f (p ⊔ p') b := by
  obtain ⟨ε, hε, hεpre⟩ := exists_small_step p p' (-b) (neg_nonneg.mpr hb)
  have hP' := tendsto_slope_dderiv f hconv p' (borderLe p p' b)
  have hP := tendsto_slope_dderiv f hconv p (borderGt p p' b)
  have hJ := tendsto_slope_dderiv f hconv (p ⊔ p') b
  apply le_of_tendsto_of_tendsto (hP'.add hP) hJ
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with t ht htε
  have hhud := dq_huddle_join f hsub p p' b hb ht (fun z hz => by
    have hh := hεpre t ht htε.le z hz
    simp only [Pi.neg_apply, mul_neg] at hh
    linarith)
  simpa [dirQuot, slope_def_field] using hhud

/-- Membership in the standalone vector subdifferential is its defining inequality. -/
theorem mem_subdiffVec_iff (f : (Fin n → ℝ) → ℝ) (x w : Fin n → ℝ) :
    SubgradVec f x w ↔ ∀ z, f x + w ⬝ᵥ (z - x) ≤ f z := Iff.rfl

/-- A finite convex function has a subgradient at every point. -/
theorem subdiff_nonempty (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (x : Fin n → ℝ) :
    {w : Fin n → ℝ | SubgradVec f x w}.Nonempty := by
  obtain ⟨w, hw, _⟩ := exists_subgrad_achieving f hconv x 0
  exact ⟨w, hw⟩

/-- The down-closure `{y : ∃ w ∈ C, y ≤ w}` equals `C + Iic 0`. -/
theorem downClosure_eq (C : Set (Fin n → ℝ)) :
    {y : Fin n → ℝ | ∃ w ∈ C, y ≤ w} = C + Set.Iic (0 : Fin n → ℝ) := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_add, Set.mem_Iic]
  constructor
  · rintro ⟨w, hw, hyw⟩
    exact ⟨w, hw, y - w, sub_nonpos.mpr hyw, by abel⟩
  · rintro ⟨w, hw, e, he, rfl⟩
    exact ⟨w, hw, by simpa using add_le_add_left he w⟩

/-- The down-closure of a compact set is closed (`compact + closed` sum). -/
theorem downClosure_closed {C : Set (Fin n → ℝ)} (hC : IsCompact C) :
    IsClosed {y : Fin n → ℝ | ∃ w ∈ C, y ≤ w} := by
  rw [downClosure_eq]; exact isClosed_Iic.add_left_of_isCompact hC

/-- The down-closure of a convex set is convex. -/
theorem downClosure_convex {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ {y : Fin n → ℝ | ∃ w ∈ C, y ≤ w} := by
  rw [downClosure_eq]; exact hC.add (convex_Iic 0)

/-- The up-closure `{y : ∃ w ∈ C, w ≤ y}` equals `C + Ici 0`. -/
theorem upClosure_eq (C : Set (Fin n → ℝ)) :
    {y : Fin n → ℝ | ∃ w ∈ C, w ≤ y} = C + Set.Ici (0 : Fin n → ℝ) := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_add, Set.mem_Ici]
  constructor
  · rintro ⟨w, hw, hwy⟩
    exact ⟨w, hw, y - w, sub_nonneg.mpr hwy, by abel⟩
  · rintro ⟨w, hw, e, he, rfl⟩
    exact ⟨w, hw, by simpa using add_le_add_left he w⟩

/-- The up-closure of a compact set is closed. -/
theorem upClosure_closed {C : Set (Fin n → ℝ)} (hC : IsCompact C) :
    IsClosed {y : Fin n → ℝ | ∃ w ∈ C, w ≤ y} := by
  rw [upClosure_eq]; exact isClosed_Ici.add_left_of_isCompact hC

/-- The up-closure of a convex set is convex. -/
theorem upClosure_convex {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ {y : Fin n → ℝ | ∃ w ∈ C, w ≤ y} := by
  rw [upClosure_eq]; exact hC.add (convex_Ici 0)

/-- **Selection (GSV Lemmas `tympani` + `diffcstartilde`, L2/L3).** If a vector `v` has
`⟨v,b⟩ ≤ f'(x;b)` for every `b ≥ 0`, then `v` is dominated by an actual subgradient at `x`:
`∃ w ∈ ∂f(x), v ≤ w`. This is the down-closure characterization of the subdifferential.

Proof plan (deferred): the down-closure `D = {y : ∃ w ∈ ∂f(x), y ≤ w}` of the (compact,
convex, nonempty — Thm 23.4 with `effectiveDomain = univ`) subdifferential is closed convex;
if `v ∉ D`, `geometric_hahn_banach_closed_point` gives `b` with `⟨v,b⟩ > sup_{y∈D}⟨y,b⟩`;
`b ≥ 0` (else the sup over the down-set is `+∞`), and then `sup_{y∈D}⟨y,b⟩ = sup_{w∈∂f(x)}⟨w,b⟩
= subdifferentialSupportAt f x b = f'(x;b)` (Thm 23.4), contradicting the hypothesis. -/
theorem exists_subgrad_ge (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (x v : Fin n → ℝ)
    (hv : ∀ b : Fin n → ℝ, 0 ≤ b → v ⬝ᵥ b ≤ dderiv f x b) :
    ∃ w : Fin n → ℝ, SubgradVec f x w ∧ v ≤ w := by
  by_contra hcon
  push_neg at hcon
  set C := {w : Fin n → ℝ | SubgradVec f x w} with hCdef
  have hvD : v ∉ {y : Fin n → ℝ | ∃ w ∈ C, y ≤ w} := by
    rintro ⟨w, hwC, hvw⟩; exact hcon w hwC hvw
  obtain ⟨φ, u, hφlt, hφv⟩ := geometric_hahn_banach_closed_point
    (downClosure_convex (subdiffVec_convex f x))
    (downClosure_closed (subdiffVec_compact f x)) hvD
  -- Represent the separating functional as a vector `b`.
  set b : Fin n → ℝ := fun i => φ (Pi.single i 1) with hbdef
  have hbridge : ∀ i : Fin n, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    intro i; funext j
    simp only [Pi.single_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hji => h hji.symm)]
  have hrep : ∀ y : Fin n → ℝ, φ y = b ⬝ᵥ y := by
    intro y
    have hpi := LinearMap.pi_apply_eq_sum_univ φ.toLinearMap y
    simp only [ContinuousLinearMap.coe_coe, hbridge] at hpi
    rw [hpi, dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [smul_eq_mul, hbdef]
    ring
  -- `b ≥ 0` (else the down-closure is unbounded in that coordinate).
  have hb_nonneg : (0 : Fin n → ℝ) ≤ b := by
    rw [Pi.le_def]; intro i; simp only [Pi.zero_apply]
    by_contra hbi; push_neg at hbi
    obtain ⟨w0, hw0C⟩ := subdiff_nonempty f hconv x
    have hsn : (0 : Fin n → ℝ) ≤ (Pi.single i 1 : Fin n → ℝ) := by
      rw [Pi.le_def]; intro j; rw [Pi.zero_apply, Pi.single_apply]; split_ifs <;> norm_num
    have hbineg : 0 < -b i := by linarith
    set t := max 0 ((u - φ w0) / (-b i)) with htdef
    have ht0 : 0 ≤ t := le_max_left _ _
    have hmemD : (w0 - t • (Pi.single i 1 : Fin n → ℝ)) ∈ {y : Fin n → ℝ | ∃ w ∈ C, y ≤ w} :=
      ⟨w0, hw0C, sub_le_self w0 (smul_nonneg ht0 hsn)⟩
    have hlt := hφlt _ hmemD
    have hval : φ (w0 - t • (Pi.single i 1 : Fin n → ℝ)) = φ w0 - t * b i := by
      rw [map_sub, map_smul, smul_eq_mul, hbdef]
    rw [hval] at hlt
    have h1 : (u - φ w0) / (-b i) ≤ t := le_max_right _ _
    have hge : u - φ w0 ≤ t * (-b i) := by
      have hh := mul_le_mul_of_nonneg_right h1 hbineg.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hbineg)] at hh
    nlinarith [hlt, hge]
  -- Hahn--Banach attainment replaces the external support-function theorem.
  obtain ⟨w, hwC, hwatt⟩ := exists_subgrad_achieving f hconv x b
  have hφw : φ w < u := hφlt w ⟨w, hwC, le_refl w⟩
  have hsup : dderiv f x b ≤ u := by
    rw [hwatt, ← dotProduct_comm, ← hrep]
    exact hφw.le
  -- Combine: `v ⬝ᵥ b ≤ f'(x;b) ≤ u < φ v = v ⬝ᵥ b`, contradiction.
  have hvb : v ⬝ᵥ b ≤ u := le_trans (hv b hb_nonneg) hsup
  have huv : u < v ⬝ᵥ b := by rw [hrep v, dotProduct_comm b v] at hφv; exact hφv
  linarith

/-- **Dual selection.** If `⟨v,b⟩ ≤ f'(x;b)` for every `b ≤ 0`, then `v` dominates some
subgradient at `x`: `∃ w ∈ ∂f(x), w ≤ v`. Mirror of `exists_subgrad_ge` with the up-closure
`{y : ∃ w ∈ ∂f(x), w ≤ y}` and directions `b ≤ 0`. -/
theorem exists_subgrad_le (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (x v : Fin n → ℝ)
    (hv : ∀ b : Fin n → ℝ, b ≤ 0 → v ⬝ᵥ b ≤ dderiv f x b) :
    ∃ w : Fin n → ℝ, SubgradVec f x w ∧ w ≤ v := by
  by_contra hcon
  push_neg at hcon
  set C := {w : Fin n → ℝ | SubgradVec f x w} with hCdef
  have hvU : v ∉ {y : Fin n → ℝ | ∃ w ∈ C, w ≤ y} := by
    rintro ⟨w, hwC, hwv⟩; exact hcon w hwC hwv
  obtain ⟨φ, u, hφlt, hφv⟩ := geometric_hahn_banach_closed_point
    (upClosure_convex (subdiffVec_convex f x))
    (upClosure_closed (subdiffVec_compact f x)) hvU
  set b : Fin n → ℝ := fun i => φ (Pi.single i 1) with hbdef
  have hbridge : ∀ i : Fin n, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    intro i; funext j
    simp only [Pi.single_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hji => h hji.symm)]
  have hrep : ∀ y : Fin n → ℝ, φ y = b ⬝ᵥ y := by
    intro y
    have hpi := LinearMap.pi_apply_eq_sum_univ φ.toLinearMap y
    simp only [ContinuousLinearMap.coe_coe, hbridge] at hpi
    rw [hpi, dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [smul_eq_mul, hbdef]
    ring
  have hb_nonpos : b ≤ (0 : Fin n → ℝ) := by
    rw [Pi.le_def]; intro i; simp only [Pi.zero_apply]
    by_contra hbi; push_neg at hbi
    obtain ⟨w0, hw0C⟩ := subdiff_nonempty f hconv x
    have hsn : (0 : Fin n → ℝ) ≤ (Pi.single i 1 : Fin n → ℝ) := by
      rw [Pi.le_def]; intro j; rw [Pi.zero_apply, Pi.single_apply]; split_ifs <;> norm_num
    set t := max 0 ((u - φ w0) / b i) with htdef
    have ht0 : 0 ≤ t := le_max_left _ _
    have hmemU : (w0 + t • (Pi.single i 1 : Fin n → ℝ)) ∈ {y : Fin n → ℝ | ∃ w ∈ C, w ≤ y} :=
      ⟨w0, hw0C, le_add_of_nonneg_right (smul_nonneg ht0 hsn)⟩
    have hlt := hφlt _ hmemU
    have hval : φ (w0 + t • (Pi.single i 1 : Fin n → ℝ)) = φ w0 + t * b i := by
      rw [map_add, map_smul, smul_eq_mul, hbdef]
    rw [hval] at hlt
    have h1 : (u - φ w0) / b i ≤ t := le_max_right _ _
    have hge : u - φ w0 ≤ t * b i := by
      have hh := mul_le_mul_of_nonneg_right h1 hbi.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hbi)] at hh
    nlinarith [hlt, hge]
  obtain ⟨w, hwC, hwatt⟩ := exists_subgrad_achieving f hconv x b
  have hφw : φ w < u := hφlt w ⟨w, hwC, le_refl w⟩
  have hsup : dderiv f x b ≤ u := by
    rw [hwatt, ← dotProduct_comm, ← hrep]
    exact hφw.le
  have hvb : v ⬝ᵥ b ≤ u := le_trans (hv b hb_nonpos) hsup
  have huv : u < v ⬝ᵥ b := by rw [hrep v, dotProduct_comm b v] at hφv; exact hφv
  linarith

/-- **Join witness** (dual of the meet `exists_subgrad_ge`, via the reflection `f(-·)`):
a subgradient at `p ⊔ p'` dominated by `mix p p' q' q`. DEFERRED (reflection bridge). -/
theorem exists_subgrad_join (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hsub : Submodular f) {p p' q q' : Fin n → ℝ}
    (hq : SubgradVec f p q) (hq' : SubgradVec f p' q') :
    ∃ qj : Fin n → ℝ, SubgradVec f (p ⊔ p') qj ∧ qj ≤ mix p p' q' q :=
  exists_subgrad_le f hconv (p ⊔ p') (mix p p' q' q) (by
    -- The **join directional inequality**: `∀ b ≤ 0, ⟨mix p p' q' q, b⟩ ≤ f'(p ⊔ p'; b)`,
    -- via `dotProduct_mix` + `subgrad_le_dderiv` + `dderiv_of_submodular_join` (join L5).
    intro b hb
    rw [dotProduct_mix]
    calc q' ⬝ᵥ borderLe p p' b + q ⬝ᵥ borderGt p p' b
        ≤ dderiv f p' (borderLe p p' b) + dderiv f p (borderGt p p' b) :=
          add_le_add (subgrad_le_dderiv f hconv hq' _) (subgrad_le_dderiv f hconv hq _)
      _ ≤ dderiv f (p ⊔ p') b := dderiv_of_submodular_join f hconv hsub p p' b hb)

/-- The Dini bridge at a general base `p + x•b` (needed for the fencing at each `x ∈ [0,1)`):
`dderiv f (p+x•b) b = derivWithin (t ↦ f(p+t•b)) (Ioi x) x`. -/
theorem dderiv_shift (f : (Fin n → ℝ) → ℝ)
    (p b : Fin n → ℝ) (x : ℝ) :
    dderiv f (p + x • b) b
      = derivWithin (fun t : ℝ => f (p + t • b)) (Set.Ioi x) x := by
  rw [dderiv]
  have hfe : (fun t : ℝ => f (p + x • b + t • b)) = (fun s : ℝ => f (p + (x + s) • b)) := by
    funext s; congr 1; rw [add_smul, add_assoc]
  have hset2 : (x : ℝ) +ᵥ Set.Ioi (0 : ℝ) = Set.Ioi x := by
    ext u; simp only [Set.mem_vadd_set, vadd_eq_add, Set.mem_Ioi]
    constructor
    · rintro ⟨v, hv, rfl⟩; linarith
    · intro h; exact ⟨u - x, by linarith, by ring⟩
  have htr := derivWithin_comp_const_add (f := fun t : ℝ => f (p + t • b))
    (a := x) (s := Set.Ioi (0:ℝ)) (x := (0:ℝ))
  rw [hset2, add_zero] at htr
  rw [hfe]; exact htr

/-- `t ↦ f(q + t•b)` is convex on ℝ (composition of convex `f` with an affine map). -/
theorem convexOn_shift (f : (Fin n → ℝ) → ℝ) (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (q b : Fin n → ℝ) : ConvexOn ℝ (Set.univ : Set ℝ) (fun t : ℝ => f (q + t • b)) := by
  have h := hconv.comp_affineMap (AffineMap.lineMap q (q + b))
  have hset : (AffineMap.lineMap q (q + b) : ℝ →ᵃ[ℝ] (Fin n → ℝ)) ⁻¹'
      (Set.univ : Set (Fin n → ℝ)) = Set.univ := by simp
  have hfun : (f ∘ (AffineMap.lineMap q (q + b) : ℝ →ᵃ[ℝ] (Fin n → ℝ)))
      = (fun t : ℝ => f (q + t • b)) := by
    funext t
    simp only [Function.comp_apply]
    congr 1
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left, add_comm]
  rwa [hset, hfun] at h

/-- **L5, backward direction** (`DD ⟹ submodular`). From the directional-derivative
inequality (`DD`, the hypothesis), submodularity follows: with `b = (p'-p)⁺`, the function
`φ(t) = f(p+t•b) - f(p∧p'+t•b)` is nonincreasing on `[0,1]` (its right derivative is `≤ 0` by
`DD` at the shifted points and the Dini bridge), so `φ(1) ≤ φ(0)`, which is submodularity. -/
theorem submodular_of_dderiv (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hDD : ∀ p p' b : Fin n → ℝ, 0 ≤ b →
      dderiv f p (borderLe p p' b) + dderiv f p' (borderGt p p' b) ≤ dderiv f (p ⊓ p') b) :
    Submodular f := by
  have hdd0 : ∀ x : Fin n → ℝ, dderiv f x 0 = 0 := dderiv_zero f
  intro p p'
  set b : Fin n → ℝ := (p' - p) ⊔ 0 with hbdef
  have hb0 : (0 : Fin n → ℝ) ≤ b := hbdef ▸ le_sup_right
  have hbz0 : ∀ z, p z ≤ p' z → b z = p' z - p z := by
    intro z h; simp only [hbdef, Pi.sup_apply, Pi.sub_apply, Pi.zero_apply]
    exact sup_eq_left.mpr (by linarith)
  have hbz0' : ∀ z, p' z < p z → b z = 0 := by
    intro z h; simp only [hbdef, Pi.sup_apply, Pi.sub_apply, Pi.zero_apply]
    exact sup_eq_right.mpr (by linarith)
  -- A, C, φ
  set A : ℝ → ℝ := fun t => f (p + t • b) with hA
  set C : ℝ → ℝ := fun t => f (p ⊓ p' + t • b) with hC
  have hAconv := convexOn_shift f hconv p b
  have hCconv := convexOn_shift f hconv (p ⊓ p') b
  have hAcont : ContinuousOn A (Set.Icc (0:ℝ) 1) :=
    (hAconv.continuousOn isOpen_univ).mono (Set.subset_univ _)
  have hCcont : ContinuousOn C (Set.Icc (0:ℝ) 1) :=
    (hCconv.continuousOn isOpen_univ).mono (Set.subset_univ _)
  -- derivative facts
  have hDA : ∀ x, HasDerivWithinAt A (derivWithin A (Set.Ioi x) x) (Set.Ici x) x := by
    intro x
    have hx : x ∈ interior (Set.univ : Set ℝ) := by rw [interior_univ]; trivial
    exact ((hAconv.hasDerivWithinAt_sInf_slope_of_mem_interior hx).differentiableWithinAt.hasDerivWithinAt).Ici_of_Ioi
  have hDC : ∀ x, HasDerivWithinAt C (derivWithin C (Set.Ioi x) x) (Set.Ici x) x := by
    intro x
    have hx : x ∈ interior (Set.univ : Set ℝ) := by rw [interior_univ]; trivial
    exact ((hCconv.hasDerivWithinAt_sInf_slope_of_mem_interior hx).differentiableWithinAt.hasDerivWithinAt).Ici_of_Ioi
  -- the bound: derivWithin A ≤ derivWithin C  (via DD at the shifted point + the Dini bridge)
  have hbound : ∀ x ∈ Set.Ico (0:ℝ) 1,
      derivWithin A (Set.Ioi x) x - derivWithin C (Set.Ioi x) x ≤ 0 := by
    rintro x ⟨hx0, hx1⟩
    -- border/meet identities at the shifted point `(p + x•b, p')`.
    have hbL : borderLe (p + x • b) p' b = b := by
      funext z
      simp only [borderLe]
      by_cases h : p z ≤ p' z
      · have hcond : (p + x • b) z ≤ p' z := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hbz0 z h]; nlinarith [hx0, hx1]
        rw [if_pos hcond]
      · have hcond : ¬ (p + x • b) z ≤ p' z := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hbz0' z (not_le.mp h), mul_zero,
            add_zero]; exact h
        rw [if_neg hcond]; exact (hbz0' z (not_le.mp h)).symm
    have hbG : borderGt (p + x • b) p' b = 0 := by
      funext z
      simp only [borderGt, Pi.zero_apply]
      by_cases h : p z ≤ p' z
      · have hcond : (p + x • b) z ≤ p' z := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hbz0 z h]; nlinarith [hx0, hx1]
        rw [if_pos hcond]
      · have hcond : ¬ (p + x • b) z ≤ p' z := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hbz0' z (not_le.mp h), mul_zero,
            add_zero]; exact h
        rw [if_neg hcond]; exact hbz0' z (not_le.mp h)
    have hmeet : (p + x • b) ⊓ p' = p ⊓ p' + x • b := by
      funext z
      simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases h : p z ≤ p' z
      · rw [inf_of_le_left (by nlinarith [hx0, hx1, hbz0 z h]),
          inf_of_le_left h, hbz0 z h]
      · have hlt := not_le.mp h
        rw [inf_of_le_right (by nlinarith [hx0, hx1, hbz0' z hlt]),
          inf_of_le_right hlt.le, hbz0' z hlt, mul_zero, add_zero]
    have hDDx := hDD (p + x • b) p' b hb0
    rw [hbL, hbG, hmeet, hdd0 p'] at hDDx
    -- `hDDx : dderiv f (p+x•b) b + 0 ≤ dderiv f (p⊓p'+x•b) b`
    rw [dderiv_shift f p b x, dderiv_shift f (p ⊓ p') b x,
      add_zero] at hDDx
    have : derivWithin A (Set.Ioi x) x ≤ derivWithin C (Set.Ioi x) x := hDDx
    linarith
  -- fencing: φ(x) ≤ φ(0) for x ∈ [0,1].
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

theorem submodular_iff_isUGS_subdiff (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) :
    Submodular f ↔ IsUGS (subdiffCorr f) := by
  constructor
  · -- (i) ⟹ (ii)
    intro hsub p p' q q' hq hq'
    obtain ⟨qm, hqm_sub, hqm_ge⟩ := exists_subgrad_ge f hconv (p ⊓ p') (mix p p' q q')
      (fun b hb => mix_dderiv_le f hconv hsub hq hq' b hb)
    obtain ⟨qj, hqj_sub, hqj_le⟩ := exists_subgrad_join f hconv hsub hq hq'
    refine ⟨qm, qj, hqm_sub, hqj_sub, fun z => ⟨fun hle => ⟨?_, ?_⟩, fun hlt => ⟨?_, ?_⟩⟩⟩
    · have h := hqm_ge z; simp only [mix] at h; rwa [if_pos hle] at h
    · have h := hqj_le z; simp only [mix] at h; rwa [if_pos hle] at h
    · have h := hqm_ge z; simp only [mix] at h; rwa [if_neg (not_le.mpr hlt)] at h
    · have h := hqj_le z; simp only [mix] at h; rwa [if_neg (not_le.mpr hlt)] at h
  · -- (ii) ⟹ (i): derive DD from UGS (via attained subgradients), then L5-backward.
    intro hUGS
    apply submodular_of_dderiv f hconv
    intro p p' b hb
    obtain ⟨q, hqC, hq⟩ := exists_subgrad_achieving f hconv p (borderLe p p' b)
    obtain ⟨q', hq'C, hq'⟩ := exists_subgrad_achieving f hconv p' (borderGt p p' b)
    obtain ⟨qm, _, hqm_sub, _, hord⟩ := hUGS p p' q q' hqC hq'C
    have hmix_le : mix p p' q q' ≤ qm := by
      intro z
      by_cases h : p z ≤ p' z
      · simpa only [mix, if_pos h] using ((hord z).1 h).1
      · simpa only [mix, if_neg h] using ((hord z).2 (not_le.mp h)).1
    have hdotle : (mix p p' q q') ⬝ᵥ b ≤ qm ⬝ᵥ b :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hmix_le z) (hb z)
    rw [hq, hq']
    calc q ⬝ᵥ borderLe p p' b + q' ⬝ᵥ borderGt p p' b
        = (mix p p' q q') ⬝ᵥ b := by rw [dotProduct_mix]
      _ ≤ qm ⬝ᵥ b := hdotle
      _ ≤ dderiv f (p ⊓ p') b := subgrad_le_dderiv f hconv hqm_sub b

/-! ## Corollary: submodular `c*` has totally isotone inverse demand -/

/-- `SubgradVec f p q` unfolded to the real subgradient inequality
`∀ z, f p + ⟨q, z - p⟩ ≤ f z`. -/
theorem subgradVec_iff (f : (Fin n → ℝ) → ℝ) (p q : Fin n → ℝ) :
    SubgradVec f p q ↔ ∀ z, f p + q ⬝ᵥ (z - p) ≤ f z :=
  mem_subdiffVec_iff f p q

/-- **The subdifferential correspondence is nonreversing** (GSV Definition 2) — with no
convexity or submodularity needed; this is exactly the equality case of subgradient
monotonicity. If `q ∈ ∂f(p)`, `q' ∈ ∂f(p')`, `p ≤ p'` and `q' ≤ q`, then the monotonicity
sum `⟨q - q', p' - p⟩ ≥ 0` is squeezed to `0` (each summand `(q_z - q'_z)(p'_z - p_z)` has
a fixed sign), forcing the two supporting inequalities at `p'`, `p` to be tight; that
tightness lets `q` support `f` at `p'` and `q'` support it at `p`. -/
theorem subdiffCorr_nonreversing (f : (Fin n → ℝ) → ℝ) :
    Nonreversing (subdiffCorr f) := by
  intro p p' q q' hq hq' hpp' hq'q
  have hqi : ∀ z, f p + q ⬝ᵥ (z - p) ≤ f z := (subgradVec_iff f p q).mp hq
  have hq'i : ∀ z, f p' + q' ⬝ᵥ (z - p') ≤ f z := (subgradVec_iff f p' q').mp hq'
  -- the two supporting inequalities that must become tight
  have hA : f p + q ⬝ᵥ (p' - p) ≤ f p' := hqi p'
  have hB : f p' + q' ⬝ᵥ (p - p') ≤ f p := hq'i p
  -- the monotonicity sum, rewritten and shown nonnegative
  have key : q ⬝ᵥ (p' - p) + q' ⬝ᵥ (p - p') = (q - q') ⬝ᵥ (p' - p) := by
    have hneg : q' ⬝ᵥ (p - p') = -(q' ⬝ᵥ (p' - p)) := by
      rw [show p - p' = -(p' - p) by abel, dotProduct_neg]
    rw [hneg, sub_dotProduct]; ring
  have hS_nonneg : (0 : ℝ) ≤ (q - q') ⬝ᵥ (p' - p) := by
    simp only [dotProduct]
    apply Finset.sum_nonneg
    intro z _
    have h1 : 0 ≤ (q - q') z := by simp only [Pi.sub_apply]; linarith [hq'q z]
    have h2 : 0 ≤ (p' - p) z := by simp only [Pi.sub_apply]; linarith [hpp' z]
    exact mul_nonneg h1 h2
  have hAB0 : q ⬝ᵥ (p' - p) + q' ⬝ᵥ (p - p') = 0 := by
    have hge : (0 : ℝ) ≤ q ⬝ᵥ (p' - p) + q' ⬝ᵥ (p - p') := by rw [key]; exact hS_nonneg
    linarith [hA, hB, hge]
  have hAeq : f p' = f p + q ⬝ᵥ (p' - p) := by linarith [hA, hB, hAB0]
  have hBeq : f p = f p' + q' ⬝ᵥ (p - p') := by linarith [hA, hB, hAB0]
  refine ⟨(subgradVec_iff f p' q).mpr ?_, (subgradVec_iff f p q').mpr ?_⟩
  · -- `q` supports `f` at `p'`
    intro y
    have hy := hqi y
    have hsplit : q ⬝ᵥ (y - p) = q ⬝ᵥ (y - p') + q ⬝ᵥ (p' - p) := by
      rw [← dotProduct_add]; congr 1; abel
    rw [hsplit] at hy
    linarith [hy, hAeq]
  · -- `q'` supports `f` at `p`
    intro y
    have hy := hq'i y
    have hsplit : q' ⬝ᵥ (y - p') = q' ⬝ᵥ (y - p) + q' ⬝ᵥ (p - p') := by
      rw [← dotProduct_add]; congr 1; abel
    rw [hsplit] at hy
    linarith [hy, hBeq]

/-- **Corollary of Theorem 3** (GSV, inverse isotonicity of demand). For a finite convex
*submodular* `c*`, its subdifferential correspondence `∂c*` has totally isotone inverse
(GSV Definition 8): it is UGS (Theorem 3, forward) and unconditionally nonreversing
(`subdiffCorr_nonreversing`), so GSV Theorem 1 upgrades it to the strong, `B`-parametrized
inverse-isotone set order. Specializing `B = ∅` yields plain inverse isotonicity — the
comparative-statics payoff: lower demand goes with lower prices. -/
theorem submodular_totallyIsotoneInverse (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (hsub : Submodular f) :
    TotallyIsotoneInverse (subdiffCorr f) :=
  (isUGS_nonreversing_iff_totallyIsotoneInverse
    ((submodular_iff_isUGS_subdiff f hconv).mp hsub)).mp (subdiffCorr_nonreversing f)

/-- **Property 2** (GSV). The subdifferential of a finite convex *submodular* function
satisfies unified gross substitutes. This is exactly the forward `(i)⟹(ii)` direction of
Theorem 3, recorded as its own named result. -/
theorem subdiff_isUGS_of_submodular (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) (hsub : Submodular f) :
    IsUGS (subdiffCorr f) :=
  (submodular_iff_isUGS_subdiff f hconv).mp hsub

end Correspondence
