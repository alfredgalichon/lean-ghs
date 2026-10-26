import UGS.KelsoCrawford
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# GSV Theorem 3 on a price domain (constant returns included)

GSV's profit-maximization theorem (Theorem 3, `spice`) is about the conjugate
`c*` of a convex cost, an extended-real-valued convex function. Its effective
domain `D = dom c*` may be a proper subset of `ℝ^N` (constant returns: `c*` is
the indicator of a closed convex set), and at boundary prices the supply
`∂c*(p)` may be empty. This file treats that case without extended reals:
`f : (Fin n → ℝ) → ℝ` is only ever evaluated on a set `D`, and subgradients are
taken relative to `D` (`SubgradOn D f p q`), which is exactly the subdifferential
of the function equal to `f` on `D` and to `+∞` off `D`.

Main results.

* `exists_meet_witness`, `exists_join_witness`: if `f` is convex and submodular
  on a convex sublattice `D`, `q ∈ ∂f(p)`, `q' ∈ ∂f(p')`, and `∂f(p ⊓ p')` is
  **nonempty**, then it contains an element dominating `mix p p' q q'` (and
  dually for the join). The proof is an exact-penalty argument: submodularity
  against the meet turns the orthant-restricted subgradient into a global one,
  and a Hahn--Banach separation produces the dominating subgradient. No
  directional derivatives, compactness, or interiority are used.
* `isUGS_subdiffOn`: hence for every sublattice `P ⊆ D` on which `∂f` is
  nonempty, the subdifferential restricted to `P` satisfies unified gross
  substitutes.
* `submodularOn_of_KCone`: conversely, one Kelso--Crawford clause on a convex
  sublattice `P ⊆ D` on which `∂f` is nonempty gives submodularity on `P`, by a
  discrete telescoping argument (no integration, no derivatives).
* `tfae_domain`: on a convex sublattice `D` where `∂f` is everywhere nonempty,
  submodularity, UGS and one-clause Kelso--Crawford are equivalent.
* `isUGS_constantReturns`: constant returns (`f = 0` on a convex sublattice `C`,
  i.e. `c* = δ_C`, supply = normal cone) always satisfy UGS on all of `C`.
* `cex_*`: a three-dimensional convex submodular `f` with `∂f` nonempty at two
  prices and empty at their meet, so the nonemptiness hypothesis cannot be
  dropped: UGS fails on `dom f`.
-/

open Matrix Filter Topology

namespace Correspondence

variable {n : ℕ}

/-! ## Definitions -/

/-- `D` is closed under coordinatewise meet and join. -/
def IsPriceSublattice (D : Set (Fin n → ℝ)) : Prop :=
  ∀ ⦃x y⦄, x ∈ D → y ∈ D → x ⊓ y ∈ D ∧ x ⊔ y ∈ D

/-- Submodularity on a set. -/
def SubmodularOnSet (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ⦃x y⦄, x ∈ D → y ∈ D → f (x ⊓ y) + f (x ⊔ y) ≤ f x + f y

/-- `q` is a subgradient of `f` at `p` **relative to `D`**: the subdifferential
of the extended-valued function equal to `f` on `D` and `+∞` elsewhere. -/
def SubgradOn (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (p q : Fin n → ℝ) : Prop :=
  ∀ x ∈ D, f p + q ⬝ᵥ (x - p) ≤ f x

/-- The supply correspondence on the price set `P`: `q ∈ Q(p)` iff `p ∈ P` and
`q ∈ ∂f(p)` (relative to `D`). -/
def subdiffOn (D P : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) → Prop :=
  fun p q => p ∈ P ∧ SubgradOn D f p q

/-- One Kelso--Crawford clause on `P`: for `x ≤ y` in `P` and `τ ∈ ∂f(y)`, some
`σ ∈ ∂f(x)` dominates `τ` on the coordinates where the price did not move. -/
def KConeOn (D P : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x ≤ y → ∀ τ, SubgradOn D f y τ →
    ∃ σ, SubgradOn D f x σ ∧ ∀ z, x z = y z → τ z ≤ σ z

/-- The other Kelso--Crawford clause on `P`: for `x ≤ y` in `P` and `σ ∈ ∂f(x)`,
some `τ ∈ ∂f(y)` is dominated by `σ` on the coordinates where the price did not move. -/
def KConeAOn (D P : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x ≤ y → ∀ σ, SubgradOn D f x σ →
    ∃ τ, SubgradOn D f y τ ∧ ∀ z, x z = y z → τ z ≤ σ z

/-- The weakest form used by the converse: for `x ≤ y` in `P` there are *some*
`σ ∈ ∂f(x)` and `τ ∈ ∂f(y)` with `τ ≤ σ` where the price did not move. Each
Kelso--Crawford clause implies it when supply is nonempty on `P`. -/
def KCpairOn (D P : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x ≤ y →
    ∃ σ τ, SubgradOn D f x σ ∧ SubgradOn D f y τ ∧ ∀ z, x z = y z → τ z ≤ σ z

theorem KConeOn.pair {D P : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) (h : KConeOn D P f) : KCpairOn D P f := by
  intro x hx y hy hxy
  obtain ⟨τ, hτ⟩ := hne y hy
  obtain ⟨σ, hσ, hdom⟩ := h x hx y hy hxy τ hτ
  exact ⟨σ, τ, hσ, hτ, hdom⟩

theorem KConeAOn.pair {D P : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) (h : KConeAOn D P f) : KCpairOn D P f := by
  intro x hx y hy hxy
  obtain ⟨σ, hσ⟩ := hne x hx
  obtain ⟨τ, hτ, hdom⟩ := h x hx y hy hxy σ hσ
  exact ⟨σ, τ, hσ, hτ, hdom⟩

/-! ## Step 1: the mix is a subgradient on the orthant above the meet -/

/-- Huddle inequality on a sublattice (GSV Lemma 6, relative form). -/
theorem huddleOn {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hDl : IsPriceSublattice D) (hsub : SubmodularOnSet D f)
    {p p' b : Fin n → ℝ} (hp : p ∈ D) (hp' : p' ∈ D) (hb : ∀ z, 0 ≤ b z)
    (hbgt : ∀ z, p' z < p z → b z ≤ p z - p' z) (hmb : p ⊓ p' + b ∈ D) :
    f (p + borderLe p p' b) + f (p' + borderGt p p' b) + f (p ⊓ p')
      ≤ f p + f p' + f (p ⊓ p' + b) := by
  have H1 := hsub hp hmb
  have hmem := hDl hp hmb
  rw [inf_meet_add p p' b hb hbgt, sup_meet_add p p' b hb hbgt] at H1 hmem
  have H2 := hsub hmem.1 hp'
  rw [inf_meetGt p p' b hb, sup_meetGt p p' b hb] at H2
  linarith

/-- Membership of the two border points, for use with subgradient inequalities. -/
theorem border_mem {D : Set (Fin n → ℝ)} (hDl : IsPriceSublattice D)
    {p p' b : Fin n → ℝ} (hp : p ∈ D) (hp' : p' ∈ D) (hb : ∀ z, 0 ≤ b z)
    (hbgt : ∀ z, p' z < p z → b z ≤ p z - p' z) (hmb : p ⊓ p' + b ∈ D) :
    p + borderLe p p' b ∈ D ∧ p' + borderGt p p' b ∈ D := by
  have hmem := hDl hp hmb
  rw [inf_meet_add p p' b hb hbgt, sup_meet_add p p' b hb hbgt] at hmem
  have h2 := (hDl hmem.1 hp').2
  rw [sup_meetGt p p' b hb] at h2
  exact ⟨hmem.2, h2⟩

/-- A small positive step fits under every positive price gap. -/
theorem exists_small_step_on (p p' b : Fin n → ℝ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ z, p' z < p z → t * b z ≤ p z - p' z := by
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ z, p' z < p z → t * b z ≤ p z - p' z := by
    rw [Filter.eventually_all]
    intro z
    by_cases h : p' z < p z
    · have ht : Tendsto (fun t : ℝ => t * b z) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun t : ℝ => t * b z) (𝓝 0) (𝓝 (0 * b z)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact (ht.eventually (gt_mem_nhds (sub_pos.mpr h))).mono fun t ht _ => ht.le
    · exact Filter.Eventually.of_forall fun t h' => absurd h' h
  have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
  have hle : ∀ᶠ t in 𝓝[>] (0:ℝ), t ≤ 1 :=
    nhdsWithin_le_nhds (Iic_mem_nhds zero_lt_one)
  obtain ⟨t, h1, h2, h3⟩ := (hpos.and (hle.and hev)).exists
  exact ⟨t, h1, h2, h3⟩

/-- **Step 1.** If `f` is convex and submodular on the convex sublattice `D` and
`q ∈ ∂f(p)`, `q' ∈ ∂f(p')`, then `mix p p' q q'` is a subgradient of `f` at
`p ⊓ p'` against every point of `D` lying above `p ⊓ p'`. -/
theorem mix_subgrad_above {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hD : Convex ℝ D) (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f)
    (hsub : SubmodularOnSet D f) {p p' q q' : Fin n → ℝ} (hp : p ∈ D) (hp' : p' ∈ D)
    (hq : SubgradOn D f p q) (hq' : SubgradOn D f p' q') :
    ∀ y ∈ D, p ⊓ p' ≤ y → f (p ⊓ p') + mix p p' q q' ⬝ᵥ (y - p ⊓ p') ≤ f y := by
  intro y hy hmy
  set m := p ⊓ p' with hm
  have hmD : m ∈ D := (hDl hp hp').1
  set b := y - m with hbdef
  have hb : ∀ z, 0 ≤ b z := fun z => by simp only [hbdef, Pi.sub_apply]; linarith [hmy z]
  obtain ⟨t, ht0, ht1, htgap⟩ := exists_small_step_on p p' b
  set tb : Fin n → ℝ := t • b with htbdef
  have htb : ∀ z, 0 ≤ tb z := fun z => by
    simp only [htbdef, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ht0.le (hb z)
  have htbgt : ∀ z, p' z < p z → tb z ≤ p z - p' z := fun z hz => by
    simp only [htbdef, Pi.smul_apply, smul_eq_mul]; exact htgap z hz
  -- the point `m + t b` is a convex combination of `m` and `y`
  have hcomb : (1 - t) • m + t • y = m + tb := by
    funext z; simp only [htbdef, hbdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply]; ring
  have hmtb : m + tb ∈ D := by
    rw [← hcomb]; exact hD hmD hy (by linarith) ht0.le (by ring)
  have hH := huddleOn hDl hsub hp hp' htb htbgt hmtb
  obtain ⟨hpL, hpG⟩ := border_mem hDl hp hp' htb htbgt hmtb
  have hqL := hq _ hpL
  have hqG := hq' _ hpG
  simp only [add_sub_cancel_left] at hqL hqG
  have hmixdot := dotProduct_mix p p' q q' tb
  -- convexity along the segment from `m` to `y`
  have hconv : f (m + tb) ≤ (1 - t) * f m + t * f y := by
    have := hf.2 hmD hy (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    rw [hcomb] at this; simpa [smul_eq_mul] using this
  have hscale : mix p p' q q' ⬝ᵥ tb = t * (mix p p' q q' ⬝ᵥ b) := by
    simp only [htbdef, dotProduct_smul, smul_eq_mul]
  -- combine: t * (mix ⬝ b) ≤ f(m+tb) - f m ≤ t * (f y - f m)
  have key : t * (mix p p' q q' ⬝ᵥ b) ≤ t * (f y - f m) := by nlinarith
  have := le_of_mul_le_mul_left key ht0
  linarith

/-! ## Step 2: the exact-penalty inequality -/

/-- The penalty function: `g(x) = Σ_z ( -r_z (x_z - m_z) + c_z (m_z - x_z)⁺ )`. -/
noncomputable def penalty (m r c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ z, (-(r z * (x z - m z)) + c z * max (m z - x z) 0)

theorem penalty_self (m r c : Fin n → ℝ) : penalty m r c m = 0 := by
  simp [penalty]

theorem continuous_penalty (m r c : Fin n → ℝ) : Continuous (penalty m r c) := by
  unfold penalty
  refine continuous_finset_sum _ fun z _ => ?_
  have h1 : Continuous fun x : Fin n → ℝ => x z := continuous_apply z
  exact ((continuous_const.mul (h1.sub continuous_const)).neg).add
    (continuous_const.mul ((continuous_const.sub h1).max continuous_const))

theorem convexOn_penalty (m r c : Fin n → ℝ) (hc : ∀ z, 0 ≤ c z) :
    ConvexOn ℝ Set.univ (penalty m r c) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [penalty, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hmax : max (m z - (a * x z + b * y z)) 0
      ≤ a * max (m z - x z) 0 + b * max (m z - y z) 0 := by
    have h1 : a * (m z - x z) ≤ a * max (m z - x z) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have h2 : b * (m z - y z) ≤ b * max (m z - y z) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hb
    have h3 : 0 ≤ a * max (m z - x z) 0 := mul_nonneg ha (le_max_right _ _)
    have h4 : 0 ≤ b * max (m z - y z) 0 := mul_nonneg hb (le_max_right _ _)
    refine max_le ?_ (by linarith)
    have : m z = a * m z + b * m z := by rw [← add_mul, hab, one_mul]
    linarith
  obtain rfl : b = 1 - a := by linarith
  have hlin : -(r z * (a * x z + (1 - a) * y z - m z))
      = a * -(r z * (x z - m z)) + (1 - a) * -(r z * (y z - m z)) := by ring
  have := mul_le_mul_of_nonneg_left hmax (hc z)
  nlinarith [this, hlin]

/-- **Step 2.** With `s₀ ∈ ∂f(m)` and weights `c_z = |s₀_z - r_z|`, the function
`f + penalty` is minimized over `D` at the meet `m = p ⊓ p'`. -/
theorem penalty_ineq {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hD : Convex ℝ D) (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f)
    (hsub : SubmodularOnSet D f) {p p' q q' s₀ : Fin n → ℝ} (hp : p ∈ D) (hp' : p' ∈ D)
    (hq : SubgradOn D f p q) (hq' : SubgradOn D f p' q')
    (hs₀ : SubgradOn D f (p ⊓ p') s₀) :
    ∀ x ∈ D, f (p ⊓ p') ≤ f x +
      penalty (p ⊓ p') (mix p p' q q') (fun z => |s₀ z - mix p p' q q' z|) x := by
  intro x hx
  set m := p ⊓ p' with hm
  set r := mix p p' q q' with hr
  have hmD : m ∈ D := (hDl hp hp').1
  have hlat := hDl hx hmD
  have hS := hsub hx hmD
  have hup := mix_subgrad_above hD hDl hf hsub hp hp' hq hq' (x ⊔ m) hlat.2 le_sup_right
  have hlow := hs₀ (x ⊓ m) hlat.1
  -- reduce to a coordinatewise nonnegativity
  have hsum : 0 ≤ r ⬝ᵥ (x ⊔ m - m) + s₀ ⬝ᵥ (x ⊓ m - m)
      + penalty m r (fun z => |s₀ z - r z|) x := by
    simp only [dotProduct, penalty, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun z _ => ?_
    simp only [Pi.sub_apply, Pi.sup_apply, Pi.inf_apply]
    rcases le_total (x z) (m z) with h | h
    · rw [sup_of_le_right h, inf_of_le_left h, max_eq_left (by linarith)]
      have habs : s₀ z - r z ≤ |s₀ z - r z| := le_abs_self _
      nlinarith
    · rw [sup_of_le_left h, inf_of_le_right h, max_eq_right (by linarith)]
      nlinarith
  linarith

/-! ## Step 3: separation produces the dominating subgradient -/

/-- If `a + α t < u` for every `t < T` (with `α > 0`), then `a + α T ≤ u`. -/
theorem le_of_forall_lt_aux {a α T u : ℝ} (hα : 0 < α)
    (H : ∀ t < T, a + α * t < u) : a + α * T ≤ u := by
  by_contra h
  push_neg at h
  set d := (a + α * T - u) / (2 * α) with hd
  have hdpos : 0 < d := div_pos (by linarith) (by linarith)
  have e : α * d = (a + α * T - u) / 2 := by rw [hd]; field_simp
  have := H (T - d) (by linarith)
  rw [mul_sub] at this
  linarith

/-- **Step 3 (sum rule, the case we need).** Let `f` be convex on the convex set
`D`, `m ∈ D`, and `g` convex and continuous on the whole space with `g m = 0`. If
`f + g` is minimized over `D` at `m`, there is `s ∈ ∂f(m)` (relative to `D`) with
`-⟨s, x - m⟩ ≤ g x` for every `x`. Proof: Hahn--Banach separation of the epigraph
of `f` from the open strict hypograph of `f m - g`. -/
theorem exists_subgrad_of_min_add {D : Set (Fin n → ℝ)} {f g : (Fin n → ℝ) → ℝ}
    (hf : ConvexOn ℝ D f) {m : Fin n → ℝ} (hm : m ∈ D)
    (hg : ConvexOn ℝ Set.univ g) (hgc : Continuous g) (hg0 : g m = 0)
    (hmin : ∀ x ∈ D, f m ≤ f x + g x) :
    ∃ s, SubgradOn D f m s ∧ ∀ x, -(s ⬝ᵥ (x - m)) ≤ g x := by
  set A : Set ((Fin n → ℝ) × ℝ) := {p | p.1 ∈ D ∧ f p.1 ≤ p.2} with hA
  set B : Set ((Fin n → ℝ) × ℝ) :=
    {p | p.1 ∈ (Set.univ : Set (Fin n → ℝ)) ∧ p.2 < (fun x => f m - g x) p.1} with hB
  have hAconv : Convex ℝ A := hf.convex_epigraph
  have hconc : ConcaveOn ℝ Set.univ (fun x => f m - g x) :=
    (concaveOn_const (f m) convex_univ).sub hg
  have hBconv : Convex ℝ B := hconc.convex_strict_hypograph
  have hBopen : IsOpen B := by
    have : B = {p : (Fin n → ℝ) × ℝ | p.2 < f m - g p.1} := by
      ext p; simp [hB]
    rw [this]
    exact isOpen_lt continuous_snd (continuous_const.sub (hgc.comp continuous_fst))
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    rintro ⟨x, t⟩ ⟨-, hxt⟩ ⟨hxD, hft⟩
    have := hmin x hxD
    simp only at hxt hft
    linarith
  obtain ⟨φ, u, hBu, hAu⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  set α := φ (0, 1) with hα
  have hφ : ∀ x t, φ (x, t) = φ (x, 0) + t * α := by
    intro x t
    have : ((x, t) : (Fin n → ℝ) × ℝ) = (x, 0) + t • ((0 : Fin n → ℝ), (1:ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  -- `α > 0` and `u = φ (m, 0) + α f m`
  have hAm : u ≤ φ (m, f m) := hAu (m, f m) ⟨hm, le_refl _⟩
  have hBm : ∀ t < f m, φ (m, 0) + α * t < u := by
    intro t ht
    have := hBu (m, t) ⟨Set.mem_univ _, by simp [hg0, ht]⟩
    rw [hφ] at this; linarith
  have hαpos : 0 < α := by
    have h1 := hBm (f m - 1) (by linarith)
    rw [hφ] at hAm
    nlinarith
  have hu : φ (m, 0) + α * f m ≤ u := le_of_forall_lt_aux hαpos hBm
  -- the linear part `ψ x = φ (x, 0)` in coordinates
  set ψ : (Fin n → ℝ) →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ) with hψ
  have hψapp : ∀ x, ψ x = φ (x, 0) := fun x => by simp [hψ]
  set s : Fin n → ℝ := fun z => -(ψ (fun j => if z = j then 1 else 0)) / α with hs
  have hsdot : ∀ v : Fin n → ℝ, s ⬝ᵥ v = -(ψ v) / α := by
    intro v
    have hpi := LinearMap.pi_apply_eq_sum_univ (ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ) v
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at hpi
    rw [hpi, dotProduct, eq_div_iff hαpos.ne', Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [hs]; field_simp
  have hsdiff : ∀ x, s ⬝ᵥ (x - m) = -(φ (x, 0) - φ (m, 0)) / α := by
    intro x; rw [hsdot, map_sub, hψapp, hψapp]
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    have h := hAu (x, f x) ⟨hx, le_refl _⟩
    rw [hφ] at h
    have key : -(φ (x, 0) - φ (m, 0)) / α ≤ f x - f m := by
      rw [div_le_iff₀ hαpos]; nlinarith
    rw [hsdiff]; linarith
  · intro x
    have hBx : ∀ t < f m - g x, φ (x, 0) + α * t < u := by
      intro t ht
      have := hBu (x, t) ⟨Set.mem_univ _, ht⟩
      rw [hφ] at this; linarith
    have h := le_of_forall_lt_aux hαpos hBx
    have hAm' := hAm
    rw [hφ] at hAm'
    rw [hsdiff, neg_div, neg_neg, div_le_iff₀ hαpos]
    nlinarith

/-! ## The meet and join witnesses -/

/-- **Meet witness.** `f` convex and submodular on the convex sublattice `D`,
`q ∈ ∂f(p)`, `q' ∈ ∂f(p')`, and `∂f(p ⊓ p') ≠ ∅`: then some `s ∈ ∂f(p ⊓ p')`
dominates `mix p p' q q'` coordinatewise. -/
theorem exists_meet_witness {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hD : Convex ℝ D) (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f)
    (hsub : SubmodularOnSet D f) {p p' q q' s₀ : Fin n → ℝ} (hp : p ∈ D) (hp' : p' ∈ D)
    (hq : SubgradOn D f p q) (hq' : SubgradOn D f p' q')
    (hs₀ : SubgradOn D f (p ⊓ p') s₀) :
    ∃ s, SubgradOn D f (p ⊓ p') s ∧ mix p p' q q' ≤ s := by
  set m := p ⊓ p'
  set r := mix p p' q q'
  set c : Fin n → ℝ := fun z => |s₀ z - r z|
  have hc : ∀ z, 0 ≤ c z := fun z => abs_nonneg _
  have hmD : m ∈ D := (hDl hp hp').1
  obtain ⟨s, hs, hsg⟩ := exists_subgrad_of_min_add hf hmD (convexOn_penalty m r c hc)
    (continuous_penalty m r c) (penalty_self m r c)
    (penalty_ineq hD hDl hf hsub hp hp' hq hq' hs₀)
  refine ⟨s, hs, fun z => ?_⟩
  have h := hsg (m + Pi.single z 1)
  have hdot : s ⬝ᵥ (m + Pi.single z 1 - m) = s z := by
    rw [add_sub_cancel_left, dotProduct_single, mul_one]
  have hpen : penalty m r c (m + Pi.single z 1) = -(r z) := by
    simp only [penalty, Pi.add_apply, add_sub_cancel_left, sub_add_cancel_left]
    rw [Finset.sum_eq_single z]
    · simp
    · intro w _ hw
      simp [hw]
    · simp
  rw [hdot, hpen] at h
  linarith

/-! ### Reflection, for the join -/

/-- The reflected function `x ↦ f (-x)` on the reflected set. -/
theorem reflect_setup {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hD : Convex ℝ D) (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f)
    (hsub : SubmodularOnSet D f) :
    Convex ℝ (-D) ∧ IsPriceSublattice (-D) ∧ ConvexOn ℝ (-D) (reflect f) ∧
      SubmodularOnSet (-D) (reflect f) := by
  have hneg_inf : ∀ x y : Fin n → ℝ, -(x ⊓ y) = -x ⊔ -y := fun x y => by
    funext z; simp only [Pi.neg_apply, Pi.inf_apply, Pi.sup_apply]; exact neg_inf _ _
  have hneg_sup : ∀ x y : Fin n → ℝ, -(x ⊔ y) = -x ⊓ -y := fun x y => by
    funext z; simp only [Pi.neg_apply, Pi.inf_apply, Pi.sup_apply]; exact neg_sup _ _
  refine ⟨hD.neg, ?_, ?_, ?_⟩
  · intro x y hx hy
    simp only [Set.mem_neg] at hx hy ⊢
    rw [hneg_inf, hneg_sup]
    exact ⟨(hDl hx hy).2, (hDl hx hy).1⟩
  · refine ⟨hD.neg, fun x hx y hy a b ha hb hab => ?_⟩
    simp only [Set.mem_neg] at hx hy
    have := hf.2 hx hy ha hb hab
    simp only [reflect, smul_eq_mul] at this ⊢
    rwa [neg_add, ← smul_neg, ← smul_neg]
  · intro x y hx hy
    simp only [Set.mem_neg] at hx hy
    have := hsub hx hy
    simp only [reflect]
    rw [hneg_inf, hneg_sup]
    linarith

theorem subgradOn_reflect {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} (p q : Fin n → ℝ) :
    SubgradOn (-D) (reflect f) p q ↔ SubgradOn D f (-p) (-q) := by
  have hd : ∀ x : Fin n → ℝ, (-q) ⬝ᵥ (x - -p) = q ⬝ᵥ (-x - p) := by
    intro x
    simp only [dotProduct, Pi.neg_apply, Pi.sub_apply]
    exact Finset.sum_congr rfl fun z _ => by ring
  constructor
  · intro h x hx
    have hx' := h (-x) (by simpa using hx)
    rw [hd x]
    simpa only [reflect, neg_neg] using hx'
  · intro h x hx
    have hx' := h (-x) hx
    rw [hd (-x)] at hx'
    simpa only [reflect, neg_neg] using hx'

/-- **Join witness.** Dually, if `∂f(p ⊔ p') ≠ ∅` it contains an element bounded
above by `q'` where `p ≤ p'` and by `q` where `p' < p`. -/
theorem exists_join_witness {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hD : Convex ℝ D) (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f)
    (hsub : SubmodularOnSet D f) {p p' q q' s₀ : Fin n → ℝ} (hp : p ∈ D) (hp' : p' ∈ D)
    (hq : SubgradOn D f p q) (hq' : SubgradOn D f p' q')
    (hs₀ : SubgradOn D f (p ⊔ p') s₀) :
    ∃ s, SubgradOn D f (p ⊔ p') s ∧
      ∀ z, (p z ≤ p' z → s z ≤ q' z) ∧ (p' z < p z → s z ≤ q z) := by
  obtain ⟨hD', hDl', hf', hsub'⟩ := reflect_setup hD hDl hf hsub
  have hmeet : -p' ⊓ -p = -(p ⊔ p') := by
    funext z; simp only [Pi.neg_apply, Pi.inf_apply, Pi.sup_apply]
    rw [neg_sup, inf_comm]
  have h1 : SubgradOn (-D) (reflect f) (-p') (-q') :=
    (subgradOn_reflect _ _).2 (by simpa using hq')
  have h2 : SubgradOn (-D) (reflect f) (-p) (-q) :=
    (subgradOn_reflect _ _).2 (by simpa using hq)
  have h0 : SubgradOn (-D) (reflect f) (-p' ⊓ -p) (-s₀) := by
    rw [hmeet]; exact (subgradOn_reflect _ _).2 (by simpa using hs₀)
  obtain ⟨s, hs, hdom⟩ := exists_meet_witness hD' hDl' hf' hsub'
    (by simpa using hp') (by simpa using hp) h1 h2 h0
  rw [hmeet] at hs
  refine ⟨-s, by simpa using (subgradOn_reflect _ _).1 hs, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · have := hdom z
    simp only [mix, Pi.neg_apply, neg_le_neg_iff, hz, if_true] at this
    simp only [Pi.neg_apply]; linarith
  · have := hdom z
    have hn : ¬ (p z ≤ p' z) := not_le.mpr hz
    simp only [mix, Pi.neg_apply, neg_le_neg_iff, hn, if_false] at this
    simp only [Pi.neg_apply]; linarith

/-! ## (i) ⟹ (ii): UGS on any sublattice of `dom ∂f` -/

/-- **Theorem 3, (i) ⟹ (ii), on a domain.** If `f` is convex and submodular on
the convex sublattice `D`, then for every sublattice `P ⊆ D` on which `∂f` is
nonempty, the subdifferential correspondence restricted to `P` satisfies unified
gross substitutes. -/
theorem isUGS_subdiffOn {D P : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hD : Convex ℝ D) (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f)
    (hsub : SubmodularOnSet D f) (hPl : IsPriceSublattice P) (hPD : P ⊆ D)
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) :
    IsUGS (subdiffOn D P f) := by
  intro p p' q q' ⟨hpP, hq⟩ ⟨hp'P, hq'⟩
  obtain ⟨hmP, hjP⟩ := hPl hpP hp'P
  obtain ⟨s₀, hs₀⟩ := hne _ hmP
  obtain ⟨s₁, hs₁⟩ := hne _ hjP
  obtain ⟨qm, hqm, hqmdom⟩ :=
    exists_meet_witness hD hDl hf hsub (hPD hpP) (hPD hp'P) hq hq' hs₀
  obtain ⟨qj, hqj, hqjdom⟩ :=
    exists_join_witness hD hDl hf hsub (hPD hpP) (hPD hp'P) hq hq' hs₁
  refine ⟨qm, qj, ⟨hmP, hqm⟩, ⟨hjP, hqj⟩, fun z => ⟨fun hz => ⟨?_, (hqjdom z).1 hz⟩,
    fun hz => ⟨?_, (hqjdom z).2 hz⟩⟩⟩
  · have := hqmdom z; simp only [mix, hz, if_true] at this; exact this
  · have := hqmdom z
    simp only [mix, not_le.mpr hz, if_false] at this; exact this

/-! ## (iii) ⟹ (i): one Kelso--Crawford clause gives submodularity -/

/-- If `h ≥ 0` vanishes off the coordinates where `x` and `y` agree, and `σ`
dominates `τ` on those coordinates, then `⟨τ, h⟩ ≤ ⟨σ, h⟩`. -/
theorem dot_le_of_tie {x y τ σ h : Fin n → ℝ} (hh : ∀ z, 0 ≤ h z)
    (hsupp : ∀ z, h z ≠ 0 → x z = y z) (hdom : ∀ z, x z = y z → τ z ≤ σ z) :
    τ ⬝ᵥ h ≤ σ ⬝ᵥ h := by
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hz : h z = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hdom z (hsupp z hz)) (hh z)

/-- **Theorem 3, (iii) ⟹ (i), on a convex sublattice.** If `P ⊆ D` is a convex
sublattice on which `∂f` is nonempty and one Kelso--Crawford clause holds on `P`,
then `f` is submodular on `P`. The proof telescopes subgradient inequalities
along the two parallel segments `[u ⊓ v, v]` and `[u, u ⊔ v]` cut into `K`
steps; the error is `⟨τ* - σ₀, v - u ⊓ v⟩ / K` and `K` is arbitrary. -/
theorem submodularOn_of_pair {D P : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hPconv : Convex ℝ P) (hPl : IsPriceSublattice P) (hPD : P ⊆ D)
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) (hKC : KCpairOn D P f) :
    SubmodularOnSet P f := by
  intro u v hu hv
  set x := u ⊓ v with hxdef
  set d : Fin n → ℝ := v - x with hddef
  obtain ⟨hxP, hjP⟩ := hPl hu hv
  have hd0 : ∀ z, 0 ≤ d z := fun z => by
    simp only [hddef, hxdef, Pi.sub_apply, Pi.inf_apply]; linarith [min_le_right (u z) (v z)]
  have hjoin : u ⊔ v = u + d := by
    funext z
    simp only [hddef, hxdef, Pi.sup_apply, Pi.add_apply, Pi.sub_apply, Pi.inf_apply]
    linarith [min_add_max (u z) (v z)]
  have hsupp : ∀ z, d z ≠ 0 → x z = u z := by
    intro z hz
    simp only [hddef, hxdef, Pi.sub_apply, Pi.inf_apply] at hz ⊢
    rcases le_total (u z) (v z) with h | h
    · exact min_eq_left h
    · rw [min_eq_right h] at hz; exact absurd (sub_self _) hz
  obtain ⟨σ₀, hσ₀⟩ := hne x hxP
  obtain ⟨τs, hτs⟩ := hne _ hjP
  set C := (τs - σ₀) ⬝ᵥ d with hC
  -- the bound for every number of steps `K`
  have hbound : ∀ K : ℕ, 0 < K →
      f (u ⊔ v) - f u - (f v - f x) ≤ C / K := by
    intro K hK
    have hKr : (0:ℝ) < K := by exact_mod_cast hK
    set h : Fin n → ℝ := (1 / (K:ℝ)) • d with hhdef
    have hh0 : ∀ z, 0 ≤ h z := fun z => by
      simp only [hhdef, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hd0 z)
    have hhsupp : ∀ z, h z ≠ 0 → d z ≠ 0 := fun z hz hdz => hz (by simp [hhdef, hdz])
    let xk : ℕ → Fin n → ℝ := fun k => x + ((k:ℝ) / K) • d
    let yk : ℕ → Fin n → ℝ := fun k => u + ((k:ℝ) / K) • d
    have hxstep : ∀ k, xk (k + 1) - xk k = h := fun k => by
      funext z; simp only [xk, hhdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast; field_simp; ring
    have hystep : ∀ k, yk k - yk (k + 1) = -h := fun k => by
      funext z; simp only [yk, hhdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.neg_apply]
      push_cast; field_simp; ring
    have ht : ∀ k, k ≤ K → (0:ℝ) ≤ (k:ℝ) / K ∧ (k:ℝ) / K ≤ 1 := fun k hk =>
      ⟨by positivity, by rw [div_le_one hKr]; exact_mod_cast hk⟩
    have hxkP : ∀ k, k ≤ K → xk k ∈ P := by
      intro k hk
      obtain ⟨h0, h1⟩ := ht k hk
      have := hPconv hxP hv (by linarith : (0:ℝ) ≤ 1 - (k:ℝ) / K) h0 (by ring)
      convert this using 1
      funext z; simp only [xk, hddef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      ring
    have hykP : ∀ k, k ≤ K → yk k ∈ P := by
      intro k hk
      obtain ⟨h0, h1⟩ := ht k hk
      have := hPconv hu hjP (by linarith : (0:ℝ) ≤ 1 - (k:ℝ) / K) h0 (by ring)
      convert this using 1
      rw [hjoin]
      funext z; simp only [yk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hxy : ∀ k, xk k ≤ yk k := fun k z => by
      simp only [xk, yk, Pi.add_apply, hxdef, Pi.inf_apply]; linarith [min_le_left (u z) (v z)]
    have htie : ∀ k z, h z ≠ 0 → xk k z = yk k z := by
      intro k z hz
      have := hsupp z (hhsupp z hz)
      simp only [xk, yk, Pi.add_apply]; rw [this]
    have hx0 : xk 0 = x := by funext z; simp [xk]
    have hy0 : yk 0 = u := by funext z; simp [yk]
    have hxK : xk K = v := by
      funext z; simp only [xk, hddef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      rw [div_self hKr.ne']; ring
    have hyK : yk K = u ⊔ v := by
      rw [hjoin]; funext z; simp only [yk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [div_self hKr.ne']; ring
    -- invariant along the first `K - 1` steps
    have inv : ∀ k, k + 1 ≤ K → ∃ σ, SubgradOn D f (xk k) σ ∧
        (f (yk k) - f u) - (f (xk k) - f x) ≤ (σ - σ₀) ⬝ᵥ h := by
      intro k
      induction k with
      | zero =>
          intro _
          refine ⟨σ₀, by rw [hx0]; exact hσ₀, ?_⟩
          rw [hx0, hy0]; simp
      | succ k ih =>
          intro hk
          obtain ⟨σ, hσ, hD⟩ := ih (by omega)
          obtain ⟨σ', τ, hσ', hτ, hdom⟩ :=
            hKC _ (hxkP (k + 1) (by omega)) _ (hykP (k + 1) (by omega)) (hxy (k + 1))
          refine ⟨σ', hσ', ?_⟩
          have hup := hτ (yk k) (hPD (hykP k (by omega)))
          rw [hystep, dotProduct_neg] at hup
          have hlow := hσ (xk (k + 1)) (hPD (hxkP (k + 1) (by omega)))
          rw [hxstep] at hlow
          have htd := dot_le_of_tie hh0 (htie (k + 1)) hdom
          rw [sub_dotProduct] at hD ⊢
          linarith
    obtain ⟨σ, hσ, hD⟩ := inv (K - 1) (by omega)
    have hK1 : K - 1 + 1 = K := by omega
    have hup := hτs (yk (K - 1)) (hPD (hykP (K - 1) (by omega)))
    have hlow := hσ (xk (K - 1 + 1)) (hPD (hxkP _ (by omega)))
    rw [hxstep] at hlow
    have hys := hystep (K - 1)
    rw [hK1, hyK] at hys
    rw [hys, dotProduct_neg] at hup
    have hxs : xk (K - 1 + 1) = v := by rw [hK1, hxK]
    rw [hxs] at hlow
    have hCh : (τs - σ₀) ⬝ᵥ h = C / K := by
      rw [hhdef, dotProduct_smul, smul_eq_mul, hC]; ring
    rw [sub_dotProduct] at hD
    rw [← hCh, sub_dotProduct]
    linarith
  -- let `K → ∞`
  by_contra hcon
  push_neg at hcon
  set Δ := f (u ⊔ v) - f u - (f v - f x) with hΔ
  have hΔpos : 0 < Δ := by rw [hΔ]; linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (max (C / Δ) 0)
  have hKpos : (0:ℝ) < K := lt_of_le_of_lt (le_max_right _ _) hK
  have hK' : 0 < K := by exact_mod_cast hKpos
  have := hbound K hK'
  have h1 : C / Δ < K := lt_of_le_of_lt (le_max_left _ _) hK
  rw [div_lt_iff₀ hΔpos] at h1
  rw [le_div_iff₀ hKpos] at this
  nlinarith

/-- **Theorem 3, (iii) ⟹ (i), on a convex sublattice**, from either
Kelso--Crawford clause. -/
theorem submodularOn_of_KCone {D P : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hPconv : Convex ℝ P) (hPl : IsPriceSublattice P) (hPD : P ⊆ D)
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) (hKC : KConeOn D P f) :
    SubmodularOnSet P f :=
  submodularOn_of_pair hPconv hPl hPD hne (hKC.pair hne)

theorem submodularOn_of_KConeA {D P : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hPconv : Convex ℝ P) (hPl : IsPriceSublattice P) (hPD : P ⊆ D)
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) (hKC : KConeAOn D P f) :
    SubmodularOnSet P f :=
  submodularOn_of_pair hPconv hPl hPD hne (hKC.pair hne)

/-- (ii) ⟹ the other clause on any price set `P`. -/
theorem KConeAOn_of_isUGS {D P : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) (hU : IsUGS (subdiffOn D P f)) :
    KConeAOn D P f := by
  intro x hx y hy hxy σ hσ
  obtain ⟨s, hs⟩ := hne y hy
  obtain ⟨τ, ⟨_, hτ⟩, hdom⟩ :=
    isUGS_kcA (Q := subdiffOn D P f) hU hxy ⟨hx, hσ⟩ ⟨hy, hs⟩
  exact ⟨τ, hτ, fun z hz => hdom z hz.symm⟩

/-- The pair condition passes to subsets of the price set. -/
theorem KCpairOn.mono {D P P' : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (h : KCpairOn D P f) (hP : P' ⊆ P) : KCpairOn D P' f :=
  fun x hx y hy hxy => h x (hP hx) y (hP hy) hxy

/-! ## The equivalence on a domain with nonempty supply -/

/-- (ii) ⟹ (iii) on any price set `P`: UGS on `P` gives the Kelso--Crawford
clause on `P`, since supply is nonempty there. -/
theorem KConeOn_of_isUGS {D P : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hne : ∀ p ∈ P, ∃ s, SubgradOn D f p s) (hU : IsUGS (subdiffOn D P f)) :
    KConeOn D P f := by
  intro x hx y hy hxy τ hτ
  obtain ⟨s, hs⟩ := hne x hx
  obtain ⟨q', ⟨_, hq'⟩, hdom⟩ :=
    isUGS_kc (Q := subdiffOn D P f) hU hxy ⟨hy, hτ⟩ ⟨hx, hs⟩
  exact ⟨q', hq', fun z hz => hdom z hz.symm⟩

/-- The Kelso--Crawford clause passes to subsets of the price set. -/
theorem KConeOn.mono {D P P' : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (h : KConeOn D P f) (hP : P' ⊆ P) : KConeOn D P' f :=
  fun x hx y hy hxy τ hτ => h x (hP hx) y (hP hy) hxy τ hτ

/-- **Theorem 3 on a domain.** On a convex sublattice `D` at every point of which
`∂f` is nonempty, submodularity of `f`, unified gross substitutes of `∂f`, and
one Kelso--Crawford clause are equivalent. Covers open domains (GSV's case) and
constant returns (`dom ∂c* = dom c*`). -/
theorem tfae_domain {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hD : Convex ℝ D) (hDl : IsPriceSublattice D) (hf : ConvexOn ℝ D f)
    (hne : ∀ p ∈ D, ∃ s, SubgradOn D f p s) :
    [SubmodularOnSet D f, IsUGS (subdiffOn D D f), KConeOn D D f].TFAE := by
  tfae_have 1 → 2 := fun hsub =>
    isUGS_subdiffOn hD hDl hf hsub hDl subset_rfl hne
  tfae_have 2 → 3 := KConeOn_of_isUGS hne
  tfae_have 3 → 1 := fun hKC =>
    submodularOn_of_KCone hD hDl subset_rfl hne hKC
  tfae_finish

/-! ## Constant returns -/

/-- Under constant returns `c* = δ_C`: the supply at `p` is the normal cone. -/
theorem subgradOn_zero_iff {C : Set (Fin n → ℝ)} (p q : Fin n → ℝ) :
    SubgradOn C (fun _ => (0:ℝ)) p q ↔ ∀ x ∈ C, q ⬝ᵥ (x - p) ≤ 0 := by
  simp [SubgradOn]

/-- **Constant returns.** If the zero-profit price set `C` is a convex
sublattice, the normal-cone supply correspondence satisfies unified gross
substitutes on all of `C`, boundary included. -/
theorem isUGS_constantReturns {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCl : IsPriceSublattice C) : IsUGS (subdiffOn C C (fun _ => (0:ℝ))) :=
  isUGS_subdiffOn hC hCl (convexOn_const 0 hC) (fun _ _ _ _ => by simp) hCl subset_rfl
    (fun p _ => ⟨0, fun x _ => by simp⟩)

/-! ## The counterexample: nonempty supply at the meet cannot be dropped -/

/-- The domain `{x₀ ≤ 0, x₁ ≤ 1, x₂ ≤ 1}` in `ℝ³`. -/
def cexD : Set (Fin 3 → ℝ) := {x | x 0 ≤ 0 ∧ x 1 ≤ 1 ∧ x 2 ≤ 1}

/-- `f(x) = -√(-x₀) · √(min (1 - x₁) (1 - x₂))`, i.e. `-√((-x₀) min(1-x₁, 1-x₂))`
on `cexD`. -/
noncomputable def cexF (x : Fin 3 → ℝ) : ℝ :=
  -(Real.sqrt (-x 0) * Real.sqrt (min (1 - x 1) (1 - x 2)))

def cexP : Fin 3 → ℝ := ![0, 1, 0]
def cexP' : Fin 3 → ℝ := ![0, 0, 1]
noncomputable def cexQ : Fin 3 → ℝ := ![1/2, 1/2, 0]
noncomputable def cexQ' : Fin 3 → ℝ := ![1/2, 0, 1/2]

theorem cex_convex : Convex ℝ cexD := by
  intro x hx y hy a b ha hb hab
  simp only [cexD, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem cex_sublattice : IsPriceSublattice cexD := by
  intro x y hx hy
  simp only [cexD, Set.mem_setOf_eq, Pi.inf_apply, Pi.sup_apply] at hx hy ⊢
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  exact ⟨⟨min_le_of_left_le hx0, min_le_of_left_le hx1, min_le_of_left_le hx2⟩,
    ⟨max_le hx0 hy0, max_le hx1 hy1, max_le hx2 hy2⟩⟩

/-- Cauchy--Schwarz in the form needed for convexity of `-√(a w)`. -/
theorem cs_aux {a b α₁ α₂ ω₁ ω₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * α₁ * ω₁ + b * α₂ * ω₂) ^ 2 ≤ (a * α₁ ^ 2 + b * α₂ ^ 2) * (a * ω₁ ^ 2 + b * ω₂ ^ 2) := by
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (α₁ * ω₂ - α₂ * ω₁))]

theorem cex_convexOn : ConvexOn ℝ cexD cexF := by
  refine ⟨cex_convex, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [cexD, Set.mem_setOf_eq] at hx hy
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  simp only [cexF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  set A₁ := -x 0; set A₂ := -y 0
  set W₁ := min (1 - x 1) (1 - x 2); set W₂ := min (1 - y 1) (1 - y 2)
  have hA₁ : 0 ≤ A₁ := by simp only [A₁]; linarith
  have hA₂ : 0 ≤ A₂ := by simp only [A₂]; linarith
  have hW₁ : 0 ≤ W₁ := le_min (by linarith) (by linarith)
  have hW₂ : 0 ≤ W₂ := le_min (by linarith) (by linarith)
  have hA : -(a * x 0 + b * y 0) = a * A₁ + b * A₂ := by simp only [A₁, A₂]; ring
  have hW : a * W₁ + b * W₂ ≤ min (1 - (a * x 1 + b * y 1)) (1 - (a * x 2 + b * y 2)) := by
    have e1 : 1 - (a * x 1 + b * y 1) = a * (1 - x 1) + b * (1 - y 1) := by
      have : (1:ℝ) = a + b := hab.symm
      nth_rewrite 1 [this]; ring
    have e2 : 1 - (a * x 2 + b * y 2) = a * (1 - x 2) + b * (1 - y 2) := by
      have : (1:ℝ) = a + b := hab.symm
      nth_rewrite 1 [this]; ring
    rw [e1, e2]
    refine le_min ?_ ?_
    · nlinarith [min_le_left (1 - x 1) (1 - x 2), min_le_left (1 - y 1) (1 - y 2)]
    · nlinarith [min_le_right (1 - x 1) (1 - x 2), min_le_right (1 - y 1) (1 - y 2)]
  rw [hA]
  set α₁ := Real.sqrt A₁; set α₂ := Real.sqrt A₂
  set ω₁ := Real.sqrt W₁; set ω₂ := Real.sqrt W₂
  have hα₁ : α₁ ^ 2 = A₁ := Real.sq_sqrt hA₁
  have hα₂ : α₂ ^ 2 = A₂ := Real.sq_sqrt hA₂
  have hω₁ : ω₁ ^ 2 = W₁ := Real.sq_sqrt hW₁
  have hω₂ : ω₂ ^ 2 = W₂ := Real.sq_sqrt hW₂
  have hα₁0 : 0 ≤ α₁ := Real.sqrt_nonneg _
  have hα₂0 : 0 ≤ α₂ := Real.sqrt_nonneg _
  have hω₁0 : 0 ≤ ω₁ := Real.sqrt_nonneg _
  have hω₂0 : 0 ≤ ω₂ := Real.sqrt_nonneg _
  set t := a * α₁ * ω₁ + b * α₂ * ω₂ with htdef
  have ht0 : 0 ≤ t := by positivity
  have hAS : 0 ≤ a * A₁ + b * A₂ := by positivity
  have hWS : 0 ≤ a * W₁ + b * W₂ := by positivity
  -- `t ≤ √(A) √(aW₁ + bW₂) ≤ √(A) √(W)`
  have hkey : t ≤ Real.sqrt (a * A₁ + b * A₂) * Real.sqrt (a * W₁ + b * W₂) := by
    rw [← Real.sqrt_mul hAS, ← Real.sqrt_sq ht0]
    apply Real.sqrt_le_sqrt
    rw [← hα₁, ← hα₂, ← hω₁, ← hω₂]
    exact cs_aux ha hb
  have hmono : Real.sqrt (a * A₁ + b * A₂) * Real.sqrt (a * W₁ + b * W₂)
      ≤ Real.sqrt (a * A₁ + b * A₂) *
        Real.sqrt (min (1 - (a * x 1 + b * y 1)) (1 - (a * x 2 + b * y 2))) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hW) (Real.sqrt_nonneg _)
  have : a * -(α₁ * ω₁) + b * -(α₂ * ω₂) = -t := by rw [htdef]; ring
  rw [this]
  linarith

/-- The real inequality behind submodularity of `cexF`. -/
theorem cex_submod_aux {a₁ a₂ w₁ w₂ wm wj : ℝ} (hm₁ : w₁ ≤ wm) (hm₂ : w₂ ≤ wm)
    (hj : min w₁ w₂ ≤ wj) :
    Real.sqrt a₁ * Real.sqrt w₁ + Real.sqrt a₂ * Real.sqrt w₂ ≤
      Real.sqrt (max a₁ a₂) * Real.sqrt wm + Real.sqrt (min a₁ a₂) * Real.sqrt wj := by
  have s1 := Real.sqrt_le_sqrt hm₁
  have s2 := Real.sqrt_le_sqrt hm₂
  have sa1 := Real.sqrt_nonneg a₁
  have sa2 := Real.sqrt_nonneg a₂
  have sw1 := Real.sqrt_nonneg w₁
  have sw2 := Real.sqrt_nonneg w₂
  rcases le_total a₁ a₂ with ha | ha
  · rw [max_eq_right ha, min_eq_left ha]
    have sa := Real.sqrt_le_sqrt ha
    rcases le_total w₁ w₂ with hw | hw
    · rw [min_eq_left hw] at hj
      have sj := Real.sqrt_le_sqrt hj
      nlinarith [mul_le_mul_of_nonneg_left s2 sa2, mul_le_mul_of_nonneg_left sj sa1]
    · rw [min_eq_right hw] at hj
      have sj := Real.sqrt_le_sqrt hj
      have sw := Real.sqrt_le_sqrt hw
      nlinarith [mul_le_mul_of_nonneg_left s1 sa2, mul_le_mul_of_nonneg_left sj sa1,
        mul_nonneg (sub_nonneg.mpr sa) (sub_nonneg.mpr sw)]
  · rw [max_eq_left ha, min_eq_right ha]
    have sa := Real.sqrt_le_sqrt ha
    rcases le_total w₁ w₂ with hw | hw
    · rw [min_eq_left hw] at hj
      have sj := Real.sqrt_le_sqrt hj
      have sw := Real.sqrt_le_sqrt hw
      nlinarith [mul_le_mul_of_nonneg_left s2 sa1, mul_le_mul_of_nonneg_left sj sa2,
        mul_nonneg (sub_nonneg.mpr sa) (sub_nonneg.mpr sw)]
    · rw [min_eq_right hw] at hj
      have sj := Real.sqrt_le_sqrt hj
      nlinarith [mul_le_mul_of_nonneg_left s1 sa1, mul_le_mul_of_nonneg_left sj sa2]

theorem cex_submodular : SubmodularOnSet cexD cexF := by
  intro x y hx hy
  simp only [cexD, Set.mem_setOf_eq] at hx hy
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  simp only [cexF, Pi.inf_apply, Pi.sup_apply]
  have hmax : -min (x 0) (y 0) = max (-x 0) (-y 0) := (max_neg_neg _ _).symm
  have hmin : -max (x 0) (y 0) = min (-x 0) (-y 0) := (min_neg_neg _ _).symm
  rw [hmax, hmin]
  have key := cex_submod_aux (a₁ := -x 0) (a₂ := -y 0)
    (w₁ := min (1 - x 1) (1 - x 2)) (w₂ := min (1 - y 1) (1 - y 2))
    (wm := min (1 - min (x 1) (y 1)) (1 - min (x 2) (y 2)))
    (wj := min (1 - max (x 1) (y 1)) (1 - max (x 2) (y 2)))
    (le_min (by have := min_le_left (x 1) (y 1); exact min_le_of_left_le (by linarith))
      (by have := min_le_left (x 2) (y 2); exact min_le_of_right_le (by linarith)))
    (le_min (by have := min_le_right (x 1) (y 1); exact min_le_of_left_le (by linarith))
      (by have := min_le_right (x 2) (y 2); exact min_le_of_right_le (by linarith)))
    (le_min
      (by
        rcases le_total (x 1) (y 1) with h | h
        · rw [max_eq_right h]
          exact min_le_of_right_le (min_le_left _ _)
        · rw [max_eq_left h]
          exact min_le_of_left_le (min_le_left _ _))
      (by
        rcases le_total (x 2) (y 2) with h | h
        · rw [max_eq_right h]
          exact min_le_of_right_le (min_le_right _ _)
        · rw [max_eq_left h]
          exact min_le_of_left_le (min_le_right _ _)))
  linarith

theorem cex_P_mem : cexP ∈ cexD := by simp [cexD, cexP]
theorem cex_P'_mem : cexP' ∈ cexD := by simp [cexD, cexP']

/-- `(1/2, 1/2, 0) ∈ ∂f(0, 1, 0)`. -/
theorem cex_subgrad_P : SubgradOn cexD cexF cexP cexQ := by
  intro x hx
  simp only [cexD, Set.mem_setOf_eq] at hx
  obtain ⟨hx0, hx1, hx2⟩ := hx
  simp only [cexF, cexP, cexQ, dotProduct, Fin.sum_univ_three, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num
  -- `√A √W ≤ √A √u ≤ (A + u)/2`, with `u = 1 - x₁ ≥ W`
  have hA : 0 ≤ -x 0 := by linarith
  have hu : 0 ≤ 1 - x 1 := by linarith
  have hWu : min (1 - x 1) (1 - x 2) ≤ 1 - x 1 := min_le_left _ _
  have s1 := Real.sqrt_le_sqrt hWu
  have sA := Real.sqrt_nonneg (-x 0)
  have hsA := Real.sq_sqrt hA
  have hsu := Real.sq_sqrt hu
  nlinarith [mul_le_mul_of_nonneg_left s1 sA, sq_nonneg (Real.sqrt (-x 0) - Real.sqrt (1 - x 1))]

/-- `(1/2, 0, 1/2) ∈ ∂f(0, 0, 1)`. -/
theorem cex_subgrad_P' : SubgradOn cexD cexF cexP' cexQ' := by
  intro x hx
  simp only [cexD, Set.mem_setOf_eq] at hx
  obtain ⟨hx0, hx1, hx2⟩ := hx
  simp only [cexF, cexP', cexQ', dotProduct, Fin.sum_univ_three, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num
  have hA : 0 ≤ -x 0 := by linarith
  have hv : 0 ≤ 1 - x 2 := by linarith
  have hWv : min (1 - x 1) (1 - x 2) ≤ 1 - x 2 := min_le_right _ _
  have s1 := Real.sqrt_le_sqrt hWv
  have sA := Real.sqrt_nonneg (-x 0)
  have hsA := Real.sq_sqrt hA
  have hsv := Real.sq_sqrt hv
  nlinarith [mul_le_mul_of_nonneg_left s1 sA, sq_nonneg (Real.sqrt (-x 0) - Real.sqrt (1 - x 2))]

theorem cex_meet : cexP ⊓ cexP' = 0 := by
  funext i; fin_cases i <;> simp [cexP, cexP']

/-- **`∂f(0) = ∅`**: along `(-ε, 0, 0)` the function drops like `-√ε`. -/
theorem cex_no_subgrad_meet : ¬ ∃ s, SubgradOn cexD cexF (cexP ⊓ cexP') s := by
  rintro ⟨s, hs⟩
  rw [cex_meet] at hs
  set t : ℝ := 1 / (|s 0| + 1) with htdef
  have ht : 0 < t := by positivity
  have hmem : (![-t ^ 2, 0, 0] : Fin 3 → ℝ) ∈ cexD := by
    simp [cexD]; positivity
  have h := hs _ hmem
  simp only [cexF, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  norm_num at h
  rw [Real.sqrt_sq ht.le] at h
  -- `t ≤ s₀ t²`, i.e. `1 ≤ s₀ t < 1`
  have h1 : 1 ≤ s 0 * t := by nlinarith
  have h2 : s 0 * t < 1 := by
    have : t * (|s 0| + 1) = 1 := by rw [htdef]; field_simp
    nlinarith [le_abs_self (s 0)]
  linarith

/-- **The counterexample.** `cexF` is convex and submodular on the convex
sublattice `cexD`; its supply is nonempty at `(0,1,0)` and `(0,0,1)` but empty
at their meet `0`; so the subdifferential on `dom f` is not UGS. -/
theorem cex_not_isUGS : ¬ IsUGS (subdiffOn cexD cexD cexF) := by
  intro h
  obtain ⟨qm, _, ⟨_, hqm⟩, _⟩ :=
    h cexP cexP' cexQ cexQ' ⟨cex_P_mem, cex_subgrad_P⟩ ⟨cex_P'_mem, cex_subgrad_P'⟩
  exact cex_no_subgrad_meet ⟨qm, hqm⟩

end Correspondence
