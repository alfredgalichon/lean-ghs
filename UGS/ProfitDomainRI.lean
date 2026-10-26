import UGS.ProfitDomain
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Semicontinuous

/-!
# The relative-interior facts behind GSV Theorem 3 on a domain

`UGS/ProfitDomain.lean` proves the two halves of the extended Theorem 3 for a
price set `P` with `∂f` nonempty on `P`. Assembling them for a general `P` with
`ri D ⊆ P ⊆ dom ∂f` uses standard relative-interior facts (Rockafellar,
*Convex Analysis*, Theorems 6.1, 6.2, 6.4, 7.5 and 23.4). Mathlib has the
relative interior (`intrinsicInterior`) and its nonemptiness, but not these
facts; this file proves the ones needed, for `D ⊆ Fin n → ℝ` convex:

* `mem_ri_iff`: `z ∈ ri D` iff `z ∈ D` and a ball around `z` in `aff D` lies in `D`;
* `ri_algebraic` / `mem_ri_of_algebraic` (Thm 6.4): `z ∈ ri D` iff for every
  `w ∈ D`, `z + ε (z - w) ∈ D` for some `ε > 0`;
* `segment_mem_ri` (Thm 6.1): `(1 - t) u + t z ∈ ri D` for `u ∈ D`, `z ∈ ri D`, `t ∈ (0, 1]`;
* `convex_ri` (Thm 6.2) and `ri_sublattice` (new: `ri` of a sublattice is a sublattice);
* `exists_subgrad_of_mem_ri` (Thm 23.4): `∂f(z) ≠ ∅` for `z ∈ ri D`;
* `submodularOn_of_ri` (Thm 7.5 in the form needed): for `f` convex and lower
  semicontinuous on `D`, submodularity on `ri D` implies submodularity on `D`.

They assemble into `theorem3_domain`, the extended Theorem 3 for every sublattice
`P` with `ri D ⊆ P ⊆ dom ∂f`.
-/

open Matrix Filter Topology Set

namespace Correspondence

variable {n : ℕ}

local notation "V" => Fin n → ℝ

/-! ## A ball characterization of the relative interior -/

theorem mem_ri_iff {D : Set V} {z : V} :
    z ∈ intrinsicInterior ℝ D ↔
      z ∈ D ∧ ∃ δ > 0, ∀ y ∈ affineSpan ℝ D, dist y z < δ → y ∈ D := by
  constructor
  · intro h
    obtain ⟨y', hy', rfl⟩ := mem_intrinsicInterior.1 h
    refine ⟨Set.mem_preimage.1
      (interior_subset (s := (Subtype.val ⁻¹' D : Set (affineSpan ℝ D))) hy'), ?_⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy'
    obtain ⟨ε, hε, hball⟩ := hy'
    refine ⟨ε, hε, fun y hy hdist => ?_⟩
    have : (⟨y, hy⟩ : affineSpan ℝ D) ∈ Metric.ball y' ε := by
      rw [Metric.mem_ball, Subtype.dist_eq]; exact hdist
    exact hball this
  · rintro ⟨hzD, δ, hδ, H⟩
    have hzS : z ∈ affineSpan ℝ D := subset_affineSpan ℝ D hzD
    refine mem_intrinsicInterior.2 ⟨⟨z, hzS⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨δ, hδ, fun y hy => ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq] at hy
    exact H y.1 y.2 hy

/-- Points of `aff D` obtained from `z ∈ aff D` by adding a difference of points of `aff D`. -/
theorem add_smul_sub_mem_span {D : Set V} {z x w : V} (hz : z ∈ affineSpan ℝ D)
    (hx : x ∈ affineSpan ℝ D) (hw : w ∈ affineSpan ℝ D) (c : ℝ) :
    z + c • (x - w) ∈ affineSpan ℝ D := by
  have hv : c • (x - w) ∈ (affineSpan ℝ D).direction :=
    Submodule.smul_mem _ c (by simpa [vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction hx hw)
  have := AffineSubspace.vadd_mem_of_mem_direction hv hz
  rwa [vadd_eq_add, add_comm] at this

/-! ## Rockafellar 6.4, 6.1, 6.2 -/

/-- **Thm 6.4, ⟹.** From a relative-interior point one can move slightly beyond,
away from any point of `D`. -/
theorem ri_algebraic {D : Set V} {z w : V} (hz : z ∈ intrinsicInterior ℝ D)
    (hw : w ∈ D) : ∃ ε : ℝ, 0 < ε ∧ z + ε • (z - w) ∈ D := by
  obtain ⟨hzD, δ, hδ, H⟩ := mem_ri_iff.1 hz
  set ε := δ / (2 * (‖z - w‖ + 1)) with hε
  have hεpos : 0 < ε := by positivity
  refine ⟨ε, hεpos, H _ ?_ ?_⟩
  · exact add_smul_sub_mem_span (subset_affineSpan ℝ D hzD) (subset_affineSpan ℝ D hzD)
      (subset_affineSpan ℝ D hw) ε
  · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hεpos.le]
    have h1 : ‖z - w‖ < ‖z - w‖ + 1 := by linarith
    calc ε * ‖z - w‖ ≤ ε * (‖z - w‖ + 1) := by nlinarith [norm_nonneg (z - w)]
      _ = δ / 2 := by rw [hε]; field_simp
      _ < δ := by linarith

/-- **Thm 6.1.** The half-open segment from a point of `D` to a relative-interior
point lies in the relative interior. -/
theorem segment_mem_ri {D : Set V} (hD : Convex ℝ D) {u z : V} (hu : u ∈ D)
    (hz : z ∈ intrinsicInterior ℝ D) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 - t) • u + t • z ∈ intrinsicInterior ℝ D := by
  obtain ⟨hzD, δ, hδ, H⟩ := mem_ri_iff.1 hz
  have hxD : (1 - t) • u + t • z ∈ D := hD hu hzD (by linarith) ht0.le (by ring)
  refine mem_ri_iff.2 ⟨hxD, t * δ, by positivity, fun y hy hdist => ?_⟩
  set x := (1 - t) • u + t • z with hx
  set y' := z + t⁻¹ • (y - x) with hy'
  have hy'S : y' ∈ affineSpan ℝ D :=
    add_smul_sub_mem_span (subset_affineSpan ℝ D hzD) hy (subset_affineSpan ℝ D hxD) _
  have hy'd : dist y' z < δ := by
    rw [hy', dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.2 ht0.le), ← dist_eq_norm]
    rw [inv_mul_lt_iff₀ ht0]; exact hdist
  have hy'D := H y' hy'S hy'd
  have hyeq : y = (1 - t) • u + t • y' := by
    rw [hy', smul_add, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul, hx]; abel
  rw [hyeq]
  exact hD hu hy'D (by linarith) ht0.le (by ring)

/-- **Thm 6.4, ⟸.** -/
theorem mem_ri_of_algebraic {D : Set V} (hD : Convex ℝ D) {z : V} (hzD : z ∈ D)
    (H : ∀ w ∈ D, ∃ ε : ℝ, 0 < ε ∧ z + ε • (z - w) ∈ D) : z ∈ intrinsicInterior ℝ D := by
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hD ⟨z, hzD⟩
  obtain ⟨ε, hε, hy⟩ := H x (intrinsicInterior_subset hx)
  have hl0 : 0 < ε / (1 + ε) := by positivity
  have hl1 : ε / (1 + ε) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have := segment_mem_ri hD hy hx hl0 hl1
  convert this using 1
  have hne : (1:ℝ) + ε ≠ 0 := by linarith
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- **Thm 6.2.** The relative interior of a convex set is convex. -/
theorem convex_ri {D : Set V} (hD : Convex ℝ D) : Convex ℝ (intrinsicInterior ℝ D) := by
  intro x hx y hy a b ha hb hab
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    have : a = 1 := by linarith
    subst this; simpa using hx
  · have := segment_mem_ri hD (intrinsicInterior_subset hx) hy hbpos (by linarith)
    rwa [show 1 - b = a by linarith] at this

/-- The algebraic margin can always be shrunk. -/
theorem algebraic_shrink {D : Set V} (hD : Convex ℝ D) {z w : V} (hz : z ∈ D) {ε ε' : ℝ}
    (hε' : 0 ≤ ε') (hle : ε' ≤ ε) (hε : 0 < ε) (h : z + ε • (z - w) ∈ D) :
    z + ε' • (z - w) ∈ D := by
  have := hD hz h (by
      have : ε' / ε ≤ 1 := (div_le_one hε).2 hle
      linarith : (0:ℝ) ≤ 1 - ε' / ε) (div_nonneg hε' hε.le) (by ring)
  convert this using 1
  rw [smul_add, smul_smul, sub_smul, one_smul]
  field_simp
  abel

/-- **The relative interior of a sublattice is a sublattice.** A common positive
rescaling and translation commute with coordinatewise meet and join. -/
theorem ri_sublattice {D : Set V} (hD : Convex ℝ D) (hDl : IsPriceSublattice D) :
    IsPriceSublattice (intrinsicInterior ℝ D) := by
  intro x y hx hy
  have hxD := intrinsicInterior_subset hx
  have hyD := intrinsicInterior_subset hy
  -- a common margin for `x` and `y` against any `w`
  have common : ∀ w ∈ D, ∃ ε : ℝ, 0 < ε ∧ x + ε • (x - w) ∈ D ∧ y + ε • (y - w) ∈ D := by
    intro w hw
    obtain ⟨ε₁, h₁, hx'⟩ := ri_algebraic hx hw
    obtain ⟨ε₂, h₂, hy'⟩ := ri_algebraic hy hw
    refine ⟨min ε₁ ε₂, lt_min h₁ h₂, ?_, ?_⟩
    · exact algebraic_shrink hD hxD (le_min h₁.le h₂.le) (min_le_left _ _) h₁ hx'
    · exact algebraic_shrink hD hyD (le_min h₁.le h₂.le) (min_le_right _ _) h₂ hy'
  have hinf : ∀ (ε : ℝ) (w : V), 0 ≤ ε →
      (x + ε • (x - w)) ⊓ (y + ε • (y - w)) = x ⊓ y + ε • (x ⊓ y - w) := by
    intro ε w hε; funext z
    simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases le_total (x z) (y z) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  have hsup : ∀ (ε : ℝ) (w : V), 0 ≤ ε →
      (x + ε • (x - w)) ⊔ (y + ε • (y - w)) = x ⊔ y + ε • (x ⊔ y - w) := by
    intro ε w hε; funext z
    simp only [Pi.sup_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases le_total (x z) (y z) with h | h
    · rw [max_eq_right h, max_eq_right (by nlinarith)]
    · rw [max_eq_left h, max_eq_left (by nlinarith)]
  refine ⟨mem_ri_of_algebraic hD (hDl hxD hyD).1 fun w hw => ?_,
    mem_ri_of_algebraic hD (hDl hxD hyD).2 fun w hw => ?_⟩
  · obtain ⟨ε, hε, h1, h2⟩ := common w hw
    exact ⟨ε, hε, by rw [← hinf ε w hε.le]; exact (hDl h1 h2).1⟩
  · obtain ⟨ε, hε, h1, h2⟩ := common w hw
    exact ⟨ε, hε, by rw [← hsup ε w hε.le]; exact (hDl h1 h2).2⟩

/-! ## Rockafellar 23.4: supply is nonempty on the relative interior -/

/-- **Thm 23.4 (nonemptiness).** A convex function on `D` has a subgradient
(relative to `D`) at every relative-interior point. The proof transports `f`
to the direction space of `aff D`, where the point becomes interior and Mathlib's
continuity of convex functions applies; the resulting local upper bound gives a
global Lipschitz-type lower bound `f z ≤ f x + L ‖x - z‖` on `D`, and the
separation lemma `exists_subgrad_of_min_add` turns it into a subgradient. -/
theorem exists_subgrad_of_mem_ri {D : Set V} {f : V → ℝ} (hD : Convex ℝ D)
    (hf : ConvexOn ℝ D f) {z : V} (hz : z ∈ intrinsicInterior ℝ D) :
    ∃ s, SubgradOn D f z s := by
  obtain ⟨hzD, δ₀, hδ₀, H⟩ := mem_ri_iff.1 hz
  have hzS : z ∈ affineSpan ℝ D := subset_affineSpan ℝ D hzD
  set W := (affineSpan ℝ D).direction
  set D' : Set W := {v | z + (v : V) ∈ D} with hD'
  set f' : W → ℝ := fun v => f (z + v) with hf'
  have hcomb : ∀ (v w : W) (a b : ℝ), a + b = 1 →
      z + ((a • v + b • w : W) : V) = a • (z + (v : V)) + b • (z + (w : V)) := by
    intro v w a b hab
    funext i
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination (-(z i)) * hab
  have hconv' : ConvexOn ℝ D' f' := by
    refine ⟨fun v hv w hw a b ha hb hab => ?_, fun v hv w hw a b ha hb hab => ?_⟩
    · show z + ((a • v + b • w : W) : V) ∈ D
      rw [hcomb v w a b hab]; exact hD hv hw ha hb hab
    · show f (z + ((a • v + b • w : W) : V)) ≤ a • f (z + v) + b • f (z + w)
      rw [hcomb v w a b hab]; exact hf.2 hv hw ha hb hab
  have h0 : (0 : W) ∈ interior D' := by
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨δ₀, hδ₀, fun v hv => ?_⟩
    rw [Metric.mem_ball, dist_zero_right] at hv
    show z + (v : V) ∈ D
    refine H _ ?_ ?_
    · have := AffineSubspace.vadd_mem_of_mem_direction v.2 hzS
      rwa [vadd_eq_add, add_comm] at this
    · rw [dist_eq_norm, add_sub_cancel_left]; exact hv
  have hcont : ContinuousAt f' 0 :=
    (hconv'.continuousOn_interior).continuousAt (isOpen_interior.mem_nhds h0)
  obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  set δ := min η δ₀ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hδη : δ < η := by have := min_le_left η δ₀; rw [hδ]; linarith
  have hδδ : δ < δ₀ := by have := min_le_right η δ₀; rw [hδ]; linarith
  -- local bound: on the relative ball of radius `δ`, `f < f z + 1`
  have hbound : ∀ y ∈ affineSpan ℝ D, ‖y - z‖ ≤ δ → y ∈ D ∧ f y < f z + 1 := by
    intro y hy hyd
    have hyD : y ∈ D := H y hy (by rw [dist_eq_norm]; linarith)
    refine ⟨hyD, ?_⟩
    have hv : y - z ∈ W := by
      simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hy hzS
    have := hηc (x := ⟨y - z, hv⟩) (by
      rw [dist_zero_right, Submodule.coe_norm]; linarith)
    simp only [hf', add_sub_cancel, ZeroMemClass.coe_zero, add_zero,
      Real.dist_eq] at this
    have h2 := (abs_lt.1 this).2
    linarith
  -- global lower bound on `D`
  have hlow : ∀ x ∈ D, f z ≤ f x + (1 / δ) * ‖x - z‖ := by
    intro x hx
    by_cases hxz : x = z
    · subst hxz; simp
    set r := ‖x - z‖ with hr
    have hrpos : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hxz)
    set y := z + (δ / r) • (z - x) with hy
    have hyS : y ∈ affineSpan ℝ D :=
      add_smul_sub_mem_span hzS hzS (subset_affineSpan ℝ D hx) _
    have hyz : ‖y - z‖ = δ := by
      rw [hy, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity),
        norm_sub_rev, ← hr]
      field_simp
    obtain ⟨hyD, hfy⟩ := hbound y hyS hyz.le
    have hsum : r / (r + δ) + δ / (r + δ) = 1 := by field_simp
    have hc := hf.2 hyD hx (by positivity) (by positivity) hsum
    have hzeq : (r / (r + δ)) • y + (δ / (r + δ)) • x = z := by
      funext i
      simp only [hy, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    rw [hzeq, smul_eq_mul, smul_eq_mul] at hc
    have key : (r + δ) * f z ≤ r * f y + δ * f x := by
      have hrd : 0 < r + δ := by positivity
      have := mul_le_mul_of_nonneg_left hc hrd.le
      rw [mul_add, ← mul_assoc, ← mul_assoc, mul_div_cancel₀ _ hrd.ne',
        mul_div_cancel₀ _ hrd.ne'] at this
      exact this
    have : f z - f x ≤ r / δ := by
      rw [le_div_iff₀ hδpos]; nlinarith
    rw [one_div_mul_eq_div]; linarith
  -- the separation lemma with `g x = (1/δ) ‖x - z‖`
  set g : V → ℝ := fun x => (1 / δ) * ‖x - z‖ with hg
  have hgconv : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [hg, smul_eq_mul]
    have e : a • x + b • y - z = a • (x - z) + b • (y - z) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination (z i) * hab
    rw [e]
    have hn : ‖a • (x - z) + b • (y - z)‖ ≤ a * ‖x - z‖ + b * ‖y - z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have hδinv : 0 ≤ 1 / δ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hn hδinv]
  have hgc : Continuous g := continuous_const.mul (continuous_id.sub continuous_const).norm
  obtain ⟨s, hs, -⟩ := exists_subgrad_of_min_add hf hzD hgconv hgc (by simp [hg]) hlow
  exact ⟨s, hs⟩

/-! ## Rockafellar 7.5, in the form needed: the limit step -/

/-- **Lemma 10 of the note.** If `f` is convex and lower semicontinuous on the
convex sublattice `D` (as `c*` is, being closed) and submodular on `ri D`, it is
submodular on `D`. Shrink toward a relative-interior point `p₀`: the four points
move along segments into `ri D`, convexity bounds the right-hand side from above
and lower semicontinuity bounds the left-hand side from below. -/
theorem submodularOn_of_ri {D : Set V} {f : V → ℝ} (hD : Convex ℝ D)
    (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f) (hlsc : LowerSemicontinuousOn f D)
    (hri : SubmodularOnSet (intrinsicInterior ℝ D) f) : SubmodularOnSet D f := by
  intro u v hu hv
  obtain ⟨p₀, hp₀⟩ := Set.Nonempty.intrinsicInterior hD ⟨u, hu⟩
  have hp₀D := intrinsicInterior_subset hp₀
  set path : V → ℝ → V := fun a t => (1 - t) • a + t • p₀ with hpath
  have hpinf : ∀ t, 0 ≤ t → t ≤ 1 → path u t ⊓ path v t = path (u ⊓ v) t := by
    intro t h0 h1; funext i
    simp only [hpath, Pi.inf_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases le_total (u i) (v i) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  have hpsup : ∀ t, 0 ≤ t → t ≤ 1 → path u t ⊔ path v t = path (u ⊔ v) t := by
    intro t h0 h1; funext i
    simp only [hpath, Pi.sup_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases le_total (u i) (v i) with h | h
    · rw [max_eq_right h, max_eq_right (by nlinarith)]
    · rw [max_eq_left h, max_eq_left (by nlinarith)]
  -- the path tends to its starting point within `D`
  have htend : ∀ a ∈ D, Tendsto (path a) (𝓝[>] 0) (𝓝[D] a) := by
    intro a ha
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous (path a) := by
        simp only [hpath]; fun_prop
      have := hc.tendsto 0
      simp only [hpath, sub_zero, one_smul, zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · have hle : ∀ᶠ t in 𝓝[>] (0:ℝ), t ≤ 1 :=
        nhdsWithin_le_nhds (Iic_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, hle] with t ht0 ht1
      exact hD ha hp₀D (by linarith) (le_of_lt ht0) (by ring)
  by_contra hcon
  have hgap : 0 < f (u ⊓ v) + f (u ⊔ v) - (f u + f v) := by linarith [not_le.1 hcon]
  set c := f (u ⊓ v) + f (u ⊔ v) - (f u + f v) with hc
  have hm := (htend _ (hDl hu hv).1).eventually
    (hlsc _ (hDl hu hv).1 (f (u ⊓ v) - c / 4) (by linarith))
  have hj := (htend _ (hDl hu hv).2).eventually
    (hlsc _ (hDl hu hv).2 (f (u ⊔ v) - c / 4) (by linarith))
  set K := |2 * f p₀ - f u - f v| + 1 with hK
  have hKpos : 0 < K := by positivity
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < c / (4 * K) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  have hle : ∀ᶠ t in 𝓝[>] (0:ℝ), t ≤ 1 := nhdsWithin_le_nhds (Iic_mem_nhds zero_lt_one)
  obtain ⟨t, hmt, hjt, hst, ht1, ht0⟩ :=
    (hm.and (hj.and (hsmall.and (hle.and (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t))))).exists
  have ht0' : (0:ℝ) < t := ht0
  have hut := segment_mem_ri hD hu hp₀ ht0' ht1
  have hvt := segment_mem_ri hD hv hp₀ ht0' ht1
  have hsubt := hri hut hvt
  rw [hpinf t ht0'.le ht1, hpsup t ht0'.le ht1] at hsubt
  have hfu := hf.2 hu hp₀D (by linarith : (0:ℝ) ≤ 1 - t) ht0'.le (by ring)
  have hfv := hf.2 hv hp₀D (by linarith : (0:ℝ) ≤ 1 - t) ht0'.le (by ring)
  simp only [smul_eq_mul] at hfu hfv
  -- `t * (2 f p₀ - f u - f v) ≤ t K < c / 4`
  have habs : t * (2 * f p₀ - f u - f v) ≤ t * K := by
    apply mul_le_mul_of_nonneg_left _ ht0'.le
    rw [hK]; linarith [le_abs_self (2 * f p₀ - f u - f v)]
  have htK : t * K < c / 4 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 4 * K)).1 hst
    linarith
  simp only [hpath] at hmt hjt hsubt
  linarith

/-! ## The extended Theorem 3 -/

/-- **Theorem 11 of the note (extended GSV Theorem 3).** Let `D` be a convex
sublattice, `f` convex and lower semicontinuous on `D` (`c*` is closed), and `P` a
sublattice with `ri D ⊆ P ⊆ dom ∂f`. Then submodularity of `f` on `D`,
submodularity on `P`, unified gross substitutes of `∂f` on `P`, each of the two
Kelso--Crawford clauses on `P`, and the weak pair condition are all equivalent. -/
theorem theorem3_domain {D P : Set V} {f : V → ℝ} (hD : Convex ℝ D)
    (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f) (hlsc : LowerSemicontinuousOn f D)
    (hPl : IsPriceSublattice P) (hriP : intrinsicInterior ℝ D ⊆ P) (hPD : P ⊆ D)
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) :
    [SubmodularOnSet D f, SubmodularOnSet P f, IsUGS (subdiffOn D P f), KConeOn D P f,
      KConeAOn D P f, KCpairOn D P f].TFAE := by
  have hriconv := convex_ri hD
  have hril := ri_sublattice hD hDl
  have hrine : ∀ p ∈ intrinsicInterior ℝ D, ∃ s, SubgradOn D f p s :=
    fun p hp => exists_subgrad_of_mem_ri hD hf hp
  tfae_have 1 → 2 := fun h x y hx hy => h (hPD hx) (hPD hy)
  tfae_have 2 → 1 := fun h =>
    submodularOn_of_ri hD hDl hf hlsc fun x y hx hy => h (hriP hx) (hriP hy)
  tfae_have 1 → 3 := fun h => isUGS_subdiffOn hD hDl hf h hPl hPD hne
  tfae_have 3 → 4 := KConeOn_of_isUGS hne
  tfae_have 3 → 5 := KConeAOn_of_isUGS hne
  tfae_have 4 → 6 := KConeOn.pair hne
  tfae_have 5 → 6 := KConeAOn.pair hne
  tfae_have 6 → 1 := fun h =>
    submodularOn_of_ri hD hDl hf hlsc
      (submodularOn_of_pair hriconv hril intrinsicInterior_subset hrine (h.mono hriP))
  tfae_finish

end Correspondence
