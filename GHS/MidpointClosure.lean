import GHS.ExchangeableConvex
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Closed midpoint-convex sets and the GHS convexity closure

This file closes the standard analytic step deferred in
`GHS.ExchangeableConvex`: a closed subset of a real normed vector space that
contains the midpoint of each pair of its points is convex.  Applied to the
closed epigraph of a lower-semicontinuous midpoint-convex function, this gives
ordinary convexity.

The proof uses compactness on each line segment.  For a target parameter
`t ∈ [0,1]`, take the greatest admissible parameter below `t` and the least
admissible parameter above `t`.  If they differed, their midpoint would be a
strictly better admissible parameter on one side, a contradiction.
-/

open Set

namespace GHS

/-- A closed set in a real normed vector space that is stable under midpoints
is convex. -/
theorem convex_of_isClosed_midpoint_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (hs : IsClosed s)
    (hmid : ∀ x ∈ s, ∀ y ∈ s, (2 : ℝ)⁻¹ • (x + y) ∈ s) : Convex ℝ s := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  have hbI : b ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact hb
    · linarith
  let φ : ℝ → E := fun t => (1 - t) • x + t • y
  have hφ : Continuous φ := by
    fun_prop
  let T : Set ℝ := Icc (0 : ℝ) 1 ∩ φ ⁻¹' s
  have hTcompact : IsCompact T :=
    isCompact_Icc.inter_right (hs.preimage hφ)
  have h0T : (0 : ℝ) ∈ T := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    simpa [φ] using hx
  have h1T : (1 : ℝ) ∈ T := by
    refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    simpa [φ] using hy
  have hTmid : ∀ u ∈ T, ∀ v ∈ T, (u + v) / 2 ∈ T := by
    intro u hu v hv
    refine ⟨⟨by linarith [hu.1.1, hv.1.1], by linarith [hu.1.2, hv.1.2]⟩, ?_⟩
    have hm := hmid (φ u) hu.2 (φ v) hv.2
    have harg : φ ((u + v) / 2) = (2 : ℝ)⁻¹ • (φ u + φ v) := by
      dsimp [φ]
      module
    change φ ((u + v) / 2) ∈ s
    rw [harg]
    exact hm
  let A : Set ℝ := T ∩ Iic b
  let B : Set ℝ := T ∩ Ici b
  have hAcompact : IsCompact A := hTcompact.inter_right isClosed_Iic
  have hBcompact : IsCompact B := hTcompact.inter_right isClosed_Ici
  have hAne : A.Nonempty := by
    refine ⟨0, h0T, ?_⟩
    exact hb
  have hBne : B.Nonempty := by
    refine ⟨1, h1T, ?_⟩
    exact hbI.2
  obtain ⟨u, huA, humax⟩ :=
    hAcompact.exists_isMaxOn hAne continuous_id.continuousOn
  obtain ⟨v, hvB, hvmin⟩ :=
    hBcompact.exists_isMinOn hBne continuous_id.continuousOn
  have huv : u = v := by
    have hu_le : u ≤ b := huA.2
    have hb_le : b ≤ v := hvB.2
    by_contra huvne
    have huvlt : u < v := lt_of_le_of_ne (hu_le.trans hb_le) huvne
    have hmT : (u + v) / 2 ∈ T := hTmid u huA.1 v hvB.1
    rcases le_total ((u + v) / 2) b with hmle | hble
    · have hmax := humax ⟨hmT, hmle⟩
      dsimp at hmax
      linarith
    · have hmin := hvmin ⟨hmT, hble⟩
      dsimp at hmin
      linarith
  have hub : u = b := by
    apply le_antisymm huA.2
    rw [huv]
    exact hvB.2
  have hbT : b ∈ T := hub ▸ huA.1
  have hcombo : a • x + b • y = φ b := by
    dsimp [φ]
    have haeq : a = 1 - b := by linarith
    rw [haeq]
  rw [hcombo]
  exact hbT.2

/-- A lower-semicontinuous midpoint-convex real-valued function is convex. -/
theorem convexOn_univ_of_lsc_midpoint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hlsc : LowerSemicontinuous f)
    (hmid : ∀ x y, 2 * f ((2 : ℝ)⁻¹ • (x + y)) ≤ f x + f y) :
    ConvexOn ℝ Set.univ f := by
  apply convexOn_of_convex_epigraph
  have hclosed : IsClosed {p : E × ℝ | p.1 ∈ Set.univ ∧ f p.1 ≤ p.2} := by
    simpa only [Set.mem_univ, true_and] using hlsc.isClosed_epigraph
  apply convex_of_isClosed_midpoint_mem hclosed
  rintro ⟨x, r⟩ ⟨-, hxr⟩ ⟨y, s⟩ ⟨-, hys⟩
  refine ⟨Set.mem_univ _, ?_⟩
  change f x ≤ r at hxr
  change f y ≤ s at hys
  have hm := hmid x y
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
  have hR : ((2 : ℝ)⁻¹ • (r + s) : ℝ) = (r + s) / 2 := by
    norm_num [smul_eq_mul]
    ring
  rw [hR]
  have hm' : f ((2 : ℝ)⁻¹ • (x + y)) ≤ (f x + f y) / 2 := by
    linarith
  exact hm'.trans (by linarith)

/-- **GHS Proposition A.1, full real-valued form.** A
lower-semicontinuous exchangeable real-valued function is convex. -/
theorem convexOn_univ_of_exchangeable [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hlsc : LowerSemicontinuous f)
    (hex : Exchangeable (fun x => (f x : ERealTop))) :
    ConvexOn ℝ Set.univ f := by
  apply convexOn_univ_of_lsc_midpoint hlsc
  intro x y
  have harg : (2 : ℝ)⁻¹ • (x + y) = (x + y) / 2 := by
    ext i
    simp [div_eq_mul_inv, mul_comm]
  rw [harg]
  exact midpoint_le_of_exchangeable hlsc hex x y

/-! ## Closed matrons -/

/-- A closed matron is midpoint-stable.  This is the set-valued version of
the compact minimization argument in `midpoint_le_of_exchangeable`. -/
theorem midpoint_mem_of_isClosed_matron [Fintype ι] {X : Set (ι → ℝ)}
    (hXclosed : IsClosed X) (hX : IsMatron X) {q q' : ι → ℝ}
    (hq : q ∈ X) (hq' : q' ∈ X) : (q + q') / 2 ∈ X := by
  classical
  set m : ι → ℝ := (q + q') / 2 with hm
  have hmi : ∀ i, m i = (q i + q' i) / 2 := fun i => rfl
  set lo : ι → ℝ := q ⊓ q' with hlo
  set hi : ι → ℝ := q ⊔ q' with hhi
  set box : Set (ι → ℝ) := Icc lo hi with hbox
  set C : Set ((ι → ℝ) × (ι → ℝ)) :=
    {p | p.1 ∈ X ∩ box} ∩ {p | p.2 ∈ X ∩ box} ∩ {p | p.1 + p.2 = q + q'} with hC
  set g₀ : ((ι → ℝ) × (ι → ℝ)) → ℝ :=
    fun p => l1Dist m p.1 + l1Dist m p.2 with hg₀
  have hg₀cont : Continuous g₀ :=
    ((continuous_l1Dist m).comp continuous_fst).add
      ((continuous_l1Dist m).comp continuous_snd)
  have hboxcompact : IsCompact box := isCompact_Icc
  have hXBclosed : IsClosed (X ∩ box) := hXclosed.inter hboxcompact.isClosed
  have hCclosed : IsClosed C := by
    exact ((hXBclosed.preimage continuous_fst).inter
      (hXBclosed.preimage continuous_snd)).inter
      (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)
  have hCsub : C ⊆ box ×ˢ box := by
    intro p hp
    exact ⟨hp.1.1.2, hp.1.2.2⟩
  have hCcompact : IsCompact C :=
    (hboxcompact.prod hboxcompact).of_isClosed_subset hCclosed hCsub
  have hqmem : (q, q') ∈ C := by
    exact ⟨⟨⟨hq, inf_le_left, le_sup_left⟩,
      ⟨hq', inf_le_right, le_sup_right⟩⟩, rfl⟩
  obtain ⟨⟨u, u'⟩, humem, humin⟩ :=
    hCcompact.exists_isMinOn ⟨(q, q'), hqmem⟩ hg₀cont.continuousOn
  have key : ∀ v v', (v, v') ∈ C → IsMinOn g₀ C (v, v') → v ≤ m := by
    intro v v' hmem hmin
    obtain ⟨⟨⟨hvX, hvbox⟩, ⟨hv'X, hv'box⟩⟩, hsum⟩ := hmem
    set δ₁ : ι → ℝ := (2⁻¹ : ℝ) • (v - v')⁺ with hδ₁def
    have hδ₁i : ∀ i, δ₁ i = (v i - v' i)⁺ / 2 := by
      intro i
      simp only [hδ₁def, Pi.smul_apply, smul_eq_mul, posPart_apply, Pi.sub_apply]
      ring
    have hδ₁mem : δ₁ ∈ Icc 0 ((v - v')⁺) := by
      constructor <;> intro i
      · rw [hδ₁i i]
        exact div_nonneg (posPart_nonneg _) (by norm_num)
      · rw [hδ₁i i]
        have hp := posPart_nonneg (v i - v' i)
        change (v i - v' i)⁺ / 2 ≤ (v i - v' i)⁺
        linarith
    obtain ⟨δ₂, hδ₂, hvnew, hv'new⟩ := hX v hvX v' hv'X δ₁ hδ₁mem
    have hsumi : ∀ i, v i + v' i = 2 * m i := by
      intro i
      have h := congrFun hsum i
      change v i + v' i = q i + q' i at h
      rw [hmi i]
      linarith
    set w : ι → ℝ := δ₁ - δ₂ with hw
    have hboxes : ∀ i, ((lo i ≤ (v - w) i ∧ (v - w) i ≤ hi i) ∧
        (lo i ≤ (v' + w) i ∧ (v' + w) i ≤ hi i)) := by
      intro i
      have h := scalar_box_step (hvbox.1 i) (hvbox.2 i) (hv'box.1 i) (hv'box.2 i)
        (hδ₁i i) (hδ₂.1 i) (hδ₂.2 i)
      simpa [hw, Pi.sub_apply, Pi.add_apply] using h
    have hvmem : (v - w, v' + w) ∈ C := by
      have hvboxnew : v - w ∈ box := by
        change v - w ∈ Icc lo hi
        exact ⟨fun i => (hboxes i).1.1, fun i => (hboxes i).1.2⟩
      have hv'boxnew : v' + w ∈ box := by
        change v' + w ∈ Icc lo hi
        exact ⟨fun i => (hboxes i).2.1, fun i => (hboxes i).2.2⟩
      refine ⟨⟨⟨hvnew, hvboxnew⟩, ⟨hv'new, hv'boxnew⟩⟩, ?_⟩
      show v - w + (v' + w) = q + q'
      calc
        v - w + (v' + w) = v + v' := by abel
        _ = q + q' := hsum
    have hdist : g₀ (v - w, v' + w) ≤
        g₀ (v, v') - 2 * ∑ i, (v i - m i)⁺ := by
      have hcoord : ∀ i, |(v - w) i - m i| + |(v' + w) i - m i|
          ≤ |v i - m i| + |v' i - m i| - 2 * (v i - m i)⁺ := by
        intro i
        have h := scalar_dist_step (hsumi i) (hδ₁i i) (hδ₂.1 i) (hδ₂.2 i)
        simpa [hw, Pi.sub_apply, Pi.add_apply] using h
      have hsum2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcoord i
      simp only [hg₀, l1Dist, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum] at hsum2 ⊢
      exact hsum2
    have hopt : g₀ (v, v') ≤ g₀ (v - w, v' + w) := hmin hvmem
    have hS : ∑ i, (v i - m i)⁺ ≤ 0 := by linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => show (0 : ℝ) ≤ (v i - m i)⁺ from posPart_nonneg _)).mp
      (le_antisymm hS (Finset.sum_nonneg fun i _ => posPart_nonneg _))
    intro i
    have hz := posPart_eq_zero.mp (hzero i (Finset.mem_univ i))
    linarith
  obtain ⟨⟨⟨huX, hubox⟩, ⟨hu'X, hu'box⟩⟩, husum⟩ := humem
  have hu_le : u ≤ m :=
    key u u' ⟨⟨⟨huX, hubox⟩, ⟨hu'X, hu'box⟩⟩, husum⟩ humin
  have hswap_mem : (u', u) ∈ C := by
    refine ⟨⟨⟨hu'X, hu'box⟩, ⟨huX, hubox⟩⟩, ?_⟩
    calc
      u' + u = u + u' := add_comm _ _
      _ = q + q' := husum
  have hswap_min : IsMinOn g₀ C (u', u) := by
    intro p hp
    calc
      g₀ (u', u) = g₀ (u, u') := by simp only [hg₀]; ring
      _ ≤ g₀ p := humin hp
  have hu'_le : u' ≤ m := key u' u hswap_mem hswap_min
  have hueq : u = m := by
    funext i
    have h := congrFun husum i
    change u i + u' i = q i + q' i at h
    have hm_i := hmi i
    linarith [hu_le i, hu'_le i]
  rwa [hueq] at huX

/-- **GHS Proposition A.1, indicator form.** Every closed matron is convex. -/
theorem convex_of_isClosed_matron [Fintype ι] {X : Set (ι → ℝ)}
    (hXclosed : IsClosed X) (hX : IsMatron X) : Convex ℝ X := by
  apply convex_of_isClosed_midpoint_mem hXclosed
  intro x hx y hy
  have hm := midpoint_mem_of_isClosed_matron hXclosed hX hx hy
  have harg : (2 : ℝ)⁻¹ • (x + y) = (x + y) / 2 := by
    ext i
    simp [div_eq_mul_inv, mul_comm]
  rwa [harg]

end GHS
