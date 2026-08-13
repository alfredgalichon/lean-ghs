import GHS.WeakSetOrder
import Mathlib.Topology.Semicontinuous

/-!
# GHS Phase 2: exchangeable ⟹ midpoint convex (Proposition 1)

`GHS.midpoint_le_of_exchangeable` formalizes the mathematical content of
**Proposition 1** of GHS Appendix B: a lower semicontinuous exchangeable
`f : (ι → ℝ) → ℝ` satisfies the midpoint inequality
`2 · f ((q + q') / 2) ≤ f q + f q'`.

This is the entirety of the paper's proof: minimize the ℓ¹ distance of the
pair to the midpoint over the compact set
`C = {(u, u') ∈ box² : u + u' = q + q', f u + f u' ≤ f q + f q'}`,
apply the exchange property with `δ₁ = (u - u')⁺ / 2`, and observe that the
exchanged pair stays in `C` while strictly approaching the midpoint unless
`u = u' = (q + q') / 2` (lemmas `scalar_box_step` and `scalar_dist_step`
coordinatewise).

*Deferred step.* The remaining implication — a midpoint-convex l.s.c. function
is convex (dyadic density) — is classical and not specific to the paper; it is
not in Mathlib and is deferred, in the same way `UGS/Submodular.lean` defers
Rockafellar's duality theorems.  What is machine-checked here is the paper's
actual argument.

*Scope note* (erratum G8): the paper states Proposition 1 for `f` real-valued
but applies it to convex indicators; the indicator (matron) version needs the
extended-real statement and is left to a later phase.
-/

open Set

namespace GHS

variable {ι : Type*}

/-! ## Scalar steps of the exchange argument -/

/-- Box stability of the exchange move, coordinatewise: if `a, b ∈ [lo, hi]`,
`d1 = (a-b)⁺/2` and `0 ≤ d2 ≤ (a-b)⁻`, then both moved points stay in
`[lo, hi]`. -/
theorem scalar_box_step {lo hi a b d1 d2 : ℝ}
    (ha1 : lo ≤ a) (ha2 : a ≤ hi) (hb1 : lo ≤ b) (hb2 : b ≤ hi)
    (hd1 : d1 = (a - b)⁺ / 2) (hd2 : 0 ≤ d2) (hd2' : d2 ≤ (a - b)⁻) :
    (lo ≤ a - (d1 - d2) ∧ a - (d1 - d2) ≤ hi) ∧
      (lo ≤ b + (d1 - d2) ∧ b + (d1 - d2) ≤ hi) := by
  rcases le_or_gt a b with hab | hab
  · -- a ≤ b: d1 = 0, the move raises a and lowers b within [a, b]
    have h1 : (a - b)⁺ = 0 := posPart_eq_zero.mpr (by linarith)
    have h2 : (a - b)⁻ = b - a := by
      have := posPart_sub_negPart (a - b); linarith
    have hd10 : d1 = 0 := by rw [hd1, h1]; ring
    have hd2b : d2 ≤ b - a := h2 ▸ hd2'
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · -- a > b: d2 = 0, both points move to the midpoint (a+b)/2
    have h1 : (a - b)⁻ = 0 := negPart_eq_zero.mpr (by linarith)
    have hd20 : d2 = 0 := le_antisymm (h1 ▸ hd2') hd2
    have h2 : (a - b)⁺ = a - b := posPart_eq_self.mpr (by linarith)
    have hd1' : d1 = (a - b) / 2 := by rw [hd1, h2]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Distance decrease of the exchange move, coordinatewise: under the sum
constraint `a + b = 2·m₀`, the move brings the pair closer to `m₀` by at least
`2·(a - m₀)⁺` in ℓ¹. -/
theorem scalar_dist_step {a b m₀ d1 d2 : ℝ} (hm : a + b = 2 * m₀)
    (hd1 : d1 = (a - b)⁺ / 2) (hd2 : 0 ≤ d2) (hd2' : d2 ≤ (a - b)⁻) :
    |a - (d1 - d2) - m₀| + |b + (d1 - d2) - m₀|
      ≤ |a - m₀| + |b - m₀| - 2 * (a - m₀)⁺ := by
  rcases le_or_gt a b with hab | hab
  · -- a ≤ b: a ≤ m₀ ≤ b, both moved points stay within [a - m₀, m₀ - a]
    have h1 : (a - b)⁺ = 0 := posPart_eq_zero.mpr (by linarith)
    have h2 : (a - b)⁻ = b - a := by
      have := posPart_sub_negPart (a - b); linarith
    have hd10 : d1 = 0 := by rw [hd1, h1]; ring
    have hd2b : d2 ≤ b - a := h2 ▸ hd2'
    have h3 : (a - m₀)⁺ = 0 := posPart_eq_zero.mpr (by linarith)
    rw [hd10, h3]
    have e1 : a - (0 - d2) - m₀ = (a - m₀) + d2 := by ring
    have e2 : b + (0 - d2) - m₀ = (b - m₀) - d2 := by ring
    rw [e1, e2]
    have hb1 : |a - m₀ + d2| ≤ m₀ - a :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hb2 : |b - m₀ - d2| ≤ m₀ - a :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have h4 : |a - m₀| = m₀ - a := by
      rw [abs_of_nonpos (by linarith)]; ring
    have h5 : |b - m₀| = b - m₀ := abs_of_nonneg (by linarith)
    linarith
  · -- a > b: both moved points land exactly on m₀
    have h1 : (a - b)⁻ = 0 := negPart_eq_zero.mpr (by linarith)
    have hd20 : d2 = 0 := le_antisymm (h1 ▸ hd2') hd2
    have h2 : (a - b)⁺ = a - b := posPart_eq_self.mpr (by linarith)
    have h3 : (a - m₀)⁺ = a - m₀ := posPart_eq_self.mpr (by linarith)
    have hd1' : d1 = (a - b) / 2 := by rw [hd1, h2]
    have e1 : a - (d1 - d2) - m₀ = 0 := by rw [hd1', hd20]; linarith
    have e2 : b + (d1 - d2) - m₀ = 0 := by rw [hd1', hd20]; linarith
    rw [e1, e2, h3, abs_zero]
    have h4 : |a - m₀| = a - m₀ := abs_of_nonneg (by linarith)
    have h5 : |b - m₀| = a - m₀ := by
      rw [abs_of_nonpos (by linarith)]; ring_nf; linarith
    linarith

/-! ## Proposition 1 (midpoint form) -/

/-- **GHS Proposition 1, midpoint form.** A lower semicontinuous exchangeable
function `f : (ι → ℝ) → ℝ` is midpoint convex:
`2 · f ((q + q') / 2) ≤ f q + f q'`.  (The classical closure — midpoint
convexity plus lower semicontinuity implies convexity — is deferred.) -/
theorem midpoint_le_of_exchangeable [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hlsc : LowerSemicontinuous f)
    (hex : Exchangeable (fun x => (f x : ERealTop))) (q q' : ι → ℝ) :
    2 * f ((q + q') / 2) ≤ f q + f q' := by
  classical
  set m : ι → ℝ := (q + q') / 2 with hm
  have hmi : ∀ i, m i = (q i + q' i) / 2 := fun i => rfl
  set lo : ι → ℝ := q ⊓ q' with hlo
  set hi : ι → ℝ := q ⊔ q' with hhi
  set box : Set (ι → ℝ) := Icc lo hi with hbox
  -- the feasible set of the auxiliary minimization
  set C : Set ((ι → ℝ) × (ι → ℝ)) :=
    {p | p.1 ∈ box} ∩ {p | p.2 ∈ box} ∩ {p | p.1 + p.2 = q + q'} ∩
      {p | f p.1 + f p.2 ≤ f q + f q'} with hC
  -- the objective: joint ℓ¹ distance to the midpoint
  set g₀ : ((ι → ℝ) × (ι → ℝ)) → ℝ := fun p => l1Dist m p.1 + l1Dist m p.2
    with hg₀
  have hg₀cont : Continuous g₀ :=
    ((continuous_l1Dist m).comp continuous_fst).add
      ((continuous_l1Dist m).comp continuous_snd)
  -- C is compact: closed subset of box × box
  have hboxcompact : IsCompact box := isCompact_Icc
  have hboxclosed : IsClosed box := hboxcompact.isClosed
  have hCclosed : IsClosed C := by
    refine (((hboxclosed.preimage continuous_fst).inter
      (hboxclosed.preimage continuous_snd)).inter
      (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)).inter ?_
    have hlsc2 : LowerSemicontinuous fun p : (ι → ℝ) × (ι → ℝ) => f p.1 + f p.2 :=
      (hlsc.comp continuous_fst).add (hlsc.comp continuous_snd)
    exact lowerSemicontinuous_iff_isClosed_preimage.mp hlsc2 (f q + f q')
  have hCsub : C ⊆ box ×ˢ box := fun p hp => ⟨hp.1.1.1, hp.1.1.2⟩
  have hCcompact : IsCompact C :=
    (hboxcompact.prod hboxcompact).of_isClosed_subset hCclosed hCsub
  -- C is nonempty: it contains (q, q')
  have hqmem : (q, q') ∈ C :=
    ⟨⟨⟨⟨inf_le_left, le_sup_left⟩, ⟨inf_le_right, le_sup_right⟩⟩, rfl⟩,
      le_refl (f q + f q')⟩
  -- attain the minimum
  obtain ⟨⟨u, u'⟩, humem, humin⟩ :=
    hCcompact.exists_isMinOn ⟨(q, q'), hqmem⟩ hg₀cont.continuousOn
  -- key step: any minimizer (u, u') has u ≤ m
  have key : ∀ v v', (v, v') ∈ C → IsMinOn g₀ C (v, v') → v ≤ m := by
    intro v v' hmem hmin
    obtain ⟨⟨⟨hv_box, hv'_box⟩, hsum⟩, hf_le⟩ := hmem
    -- the exchange move with δ₁ = (v - v')⁺ / 2
    set δ₁ : ι → ℝ := (2⁻¹ : ℝ) • (v - v')⁺ with hδ₁def
    have hδ₁i : ∀ i, δ₁ i = (v i - v' i)⁺ / 2 := by
      intro i
      simp only [hδ₁def, Pi.smul_apply, smul_eq_mul, posPart_apply, Pi.sub_apply]
      ring
    have hδ₁mem : δ₁ ∈ Icc 0 ((v - v')⁺) := by
      constructor <;> intro i
      · have h0 := posPart_nonneg (v i - v' i)
        show (0:ℝ) ≤ δ₁ i
        rw [hδ₁i i]
        linarith
      · have h0 := posPart_nonneg (v i - v' i)
        show δ₁ i ≤ (v - v')⁺ i
        rw [hδ₁i i, show (v - v')⁺ i = (v i - v' i)⁺ from rfl]
        linarith
    obtain ⟨δ₂, hδ₂, hkey⟩ := hex v v' δ₁ hδ₁mem
    simp only [← WithTop.coe_add, WithTop.coe_le_coe] at hkey
    -- coordinate data for the two scalar lemmas
    have hδ₂0 : ∀ i, 0 ≤ δ₂ i := fun i => hδ₂.1 i
    have hδ₂' : ∀ i, δ₂ i ≤ (v i - v' i)⁻ := fun i => hδ₂.2 i
    have hsumi : ∀ i, v i + v' i = 2 * m i := by
      intro i
      have := congrFun hsum i
      have hqi : (q + q') i = q i + q' i := rfl
      rw [hmi i]
      have : v i + v' i = q i + q' i := this
      linarith
    -- the moved pair
    set w : ι → ℝ := δ₁ - δ₂ with hw
    have hboxes : ∀ i, ((lo i ≤ (v - w) i ∧ (v - w) i ≤ hi i) ∧
        (lo i ≤ (v' + w) i ∧ (v' + w) i ≤ hi i)) := by
      intro i
      have h := scalar_box_step (hv_box.1 i) (hv_box.2 i) (hv'_box.1 i) (hv'_box.2 i)
        (hδ₁i i) (hδ₂0 i) (hδ₂' i)
      simpa [hw, Pi.sub_apply, Pi.add_apply] using h
    have hvmem : (v - w, v' + w) ∈ C := by
      refine ⟨⟨⟨⟨fun i => (hboxes i).1.1, fun i => (hboxes i).1.2⟩,
        ⟨fun i => (hboxes i).2.1, fun i => (hboxes i).2.2⟩⟩, ?_⟩, ?_⟩
      · show v - w + (v' + w) = q + q'
        have h1 : v - w + (v' + w) = v + v' := by abel
        rw [h1]
        exact hsum
      · show f (v - w) + f (v' + w) ≤ f q + f q'
        have h2 : f v + f v' ≤ f q + f q' := hf_le
        calc f (v - w) + f (v' + w) ≤ f v + f v' := by
              simpa [hw] using hkey
          _ ≤ f q + f q' := h2
    -- the move decreases the objective by 2·∑ (v i - m i)⁺
    have hdist : g₀ (v - w, v' + w) ≤ g₀ (v, v') - 2 * ∑ i, (v i - m i)⁺ := by
      have hcoord : ∀ i, |(v - w) i - m i| + |(v' + w) i - m i|
          ≤ |v i - m i| + |v' i - m i| - 2 * (v i - m i)⁺ := by
        intro i
        have h := scalar_dist_step (hsumi i) (hδ₁i i) (hδ₂0 i) (hδ₂' i)
        simpa [hw, Pi.sub_apply, Pi.add_apply] using h
      have hsum2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcoord i
      have hL : g₀ (v - w, v' + w) = ∑ i, (|(v - w) i - m i| + |(v' + w) i - m i|) := by
        simp only [hg₀, l1Dist, Finset.sum_add_distrib]
      have hR : g₀ (v, v') - 2 * ∑ i, (v i - m i)⁺
          = ∑ i, (|v i - m i| + |v' i - m i| - 2 * (v i - m i)⁺) := by
        simp only [hg₀, l1Dist, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
      rw [hL, hR]
      exact hsum2
    -- minimality forces ∑ (v i - m i)⁺ = 0, i.e. v ≤ m
    have hopt : g₀ (v, v') ≤ g₀ (v - w, v' + w) := hmin hvmem
    have hS : ∑ i, (v i - m i)⁺ ≤ 0 := by linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => show (0:ℝ) ≤ (v i - m i)⁺ from posPart_nonneg _)).mp
      (le_antisymm hS (Finset.sum_nonneg fun i _ =>
        show (0:ℝ) ≤ (v i - m i)⁺ from posPart_nonneg _))
    intro i
    have := posPart_eq_zero.mp (hzero i (Finset.mem_univ i))
    linarith
  -- apply the key step to (u, u') and to the swapped pair (u', u)
  obtain ⟨⟨⟨hu_box, hu'_box⟩, husum⟩, huf⟩ := humem
  have hu_le : u ≤ m :=
    key u u' ⟨⟨⟨hu_box, hu'_box⟩, husum⟩, huf⟩ humin
  have hswap_mem : (u', u) ∈ C := by
    refine ⟨⟨⟨hu'_box, hu_box⟩, ?_⟩, ?_⟩
    · show u' + u = q + q'
      rw [add_comm u' u]
      exact husum
    · show f u' + f u ≤ f q + f q'
      have h : f u + f u' ≤ f q + f q' := huf
      linarith
  have hswap_min : IsMinOn g₀ C (u', u) := by
    intro p hp
    have h1 : g₀ (u', u) = g₀ (u, u') := by
      simp only [hg₀]; ring
    calc g₀ (u', u) = g₀ (u, u') := h1
      _ ≤ g₀ p := humin hp
  have hu'_le : u' ≤ m := key u' u hswap_mem hswap_min
  -- u ≤ m, u' ≤ m and u + u' = 2m force u = u' = m
  have hueq : u = m := by
    funext i
    have h1 := hu_le i
    have h2 := hu'_le i
    have h3 := congrFun husum i
    have : u i + u' i = q i + q' i := h3
    have hm2 : m i = (q i + q' i) / 2 := hmi i
    linarith
  have hu'eq : u' = m := by
    funext i
    have h3 := congrFun husum i
    have : u i + u' i = q i + q' i := h3
    have := congrFun hueq i
    have hm2 : m i = (q i + q' i) / 2 := hmi i
    linarith
  -- conclude from (u, u') ∈ C
  rw [hueq, hu'eq] at huf
  have hfinal : f m + f m ≤ f q + f q' := huf
  linarith

end GHS
