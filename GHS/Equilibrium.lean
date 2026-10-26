import GHS.OrthantDuality

/-!
# GHS Phase 6: Theorem 3, ε-equilibrium form

The waiting-time decomposition of Theorem 3's limit, in the sharp finite
form.  The paper compactifies waiting times into `ℝ̄₊ = [0, ∞]` to force
attainment; at finite `τ` the correct statement is the ε-form, and it
follows from `theorem3_limit` (the τ-free limit identification) combined
with the ε-strong duality of `GHS/OrthantDuality.lean`:

* `exists_approx_kkt` — a box-optimal acceptance `μ` admits, for every
  `ε > 0`, a waiting-time vector `τ ≥ 0` with Fenchel–Young ε-tight at
  `(μ, α - τ)` (i.e. `μ ∈ ∂_ε G(α - τ)`) and ε-complementary slackness
  `τᵀ(q̄ - μ) ≤ ε`;
* `theorem3_eps_equilibrium` — **Theorem 3, ε-equilibrium form**: Algorithm
  1's limit `(μ, Ainf)` satisfies, for every `ε > 0`: on the proposing side
  there is `τα ≥ 0` with `μ ∈ ∂_ε G(α - τα)` and `ταᵀ(Ainf - μ) ≤ ε`; on
  the disposing side there is `τγ ≥ 0` with `μ ∈ ∂_ε H(γ - τγ)` (there the
  capacity is `μ` itself, so complementary slackness is exact).  Together
  with the memberships `Ainf - μ ∈ rejectSet_G(α, Ainf)` and
  `0 ∈ rejectSet_H(γ, μ)` this is the generalized-equilibrium content of
  the paper's Theorem 3 at finite waiting times.

Mathlib-only (part of the standalone `GHS` target).
-/

open Set Filter Topology

namespace GHS

namespace WelfareDual

variable {ι : Type*} [Fintype ι] (W : WelfareDual ι)

/-- **Approximate Kuhn–Tucker multipliers.** If `μ` attains the box value at
capacity `q̄`, then for every `ε > 0` some `τ ≥ 0` makes Fenchel–Young
ε-tight at `(μ, α - τ)` with ε-complementary slackness. -/
theorem exists_approx_kkt (hDconv : Convex ℝ W.D)
    (hcost_conv : ConvexOn ℝ W.D W.cost) (α : ι → ℝ) {qb μ : ι → ℝ}
    (hqb : 0 ≤ qb) (hμD : μ ∈ W.D) (hle : μ ≤ qb)
    (hopt : W.boxValue α qb = μ ⬝ᵥ α - W.cost μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ, 0 ≤ τ ∧
      μ ⬝ᵥ (α - τ) - W.cost μ ≤ W.Gfn (α - τ) ∧
      W.Gfn (α - τ) ≤ μ ⬝ᵥ (α - τ) - W.cost μ + ε ∧
      0 ≤ τ ⬝ᵥ (qb - μ) ∧ τ ⬝ᵥ (qb - μ) ≤ ε := by
  obtain ⟨τ, hτ0, hτval⟩ := W.exists_dual_near hDconv hcost_conv α hqb hε
  rw [hopt] at hτval
  have hFY : μ ⬝ᵥ (α - τ) - W.cost μ ≤ W.Gfn (α - τ) := W.le_Gfn hμD
  have hsl : 0 ≤ τ ⬝ᵥ (qb - μ) := by
    simp only [dotProduct, Pi.sub_apply]
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 : (0:ℝ) ≤ τ i := hτ0 i
    have h2 : μ i ≤ qb i := hle i
    nlinarith
  have h1 : τ ⬝ᵥ (qb - μ) = τ ⬝ᵥ qb - τ ⬝ᵥ μ := dotProduct_sub _ _ _
  have h2 : μ ⬝ᵥ (α - τ) = μ ⬝ᵥ α - μ ⬝ᵥ τ := dotProduct_sub _ _ _
  have h3 : qb ⬝ᵥ τ = τ ⬝ᵥ qb := dotProduct_comm _ _
  have h4 : μ ⬝ᵥ τ = τ ⬝ᵥ μ := dotProduct_comm _ _
  exact ⟨τ, hτ0, hFY, by linarith, hsl, by linarith⟩

end WelfareDual

variable {ι : Type*} [Fintype ι] {WG WH : WelfareDual ι} {α γ : ι → ℝ}

/-- **GHS Theorem 3, ε-equilibrium form.** Run Algorithm 1 from a
nonnegative initial availability, with exchangeable proposer cost and
convex welfare data on both sides.  The limit `(μ, Ainf)` satisfies the
τ-free memberships (`μ` proposer-optimal at `Ainf`, disposal fixed point),
and for every `ε > 0` admits nonnegative waiting times: `τα` with
`μ ∈ ∂_ε G(α - τα)` and `ταᵀ(Ainf - μ) ≤ ε` on the proposing side, `τγ`
with `μ ∈ ∂_ε H(γ - τγ)` on the disposing side. -/
theorem theorem3_eps_equilibrium (hcG : Exchangeable WG.cFn)
    (hDG : ∀ μ ∈ WG.D, 0 ≤ μ) (hDH : ∀ μ ∈ WH.D, 0 ≤ μ)
    (hDGconv : Convex ℝ WG.D) (hcostG_conv : ConvexOn ℝ WG.D WG.cost)
    (hDHconv : Convex ℝ WH.D) (hcostH_conv : ConvexOn ℝ WH.D WH.cost)
    {A0 : ι → ℝ} (hA0 : 0 ≤ A0) :
    ∃ (s : DASequences ι) (μ : ι → ℝ), s.A 0 = A0 ∧ 0 ≤ μ ∧ μ ≤ s.Ainf ∧
      s.Ainf - μ ∈ WG.rejectSet α s.Ainf ∧ 0 ∈ WH.rejectSet γ μ ∧
      (∀ ε : ℝ, 0 < ε → ∃ τα, 0 ≤ τα ∧
        μ ⬝ᵥ (α - τα) - WG.cost μ ≤ WG.Gfn (α - τα) ∧
        WG.Gfn (α - τα) ≤ μ ⬝ᵥ (α - τα) - WG.cost μ + ε ∧
        τα ⬝ᵥ (s.Ainf - μ) ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ τγ, 0 ≤ τγ ∧
        μ ⬝ᵥ (γ - τγ) - WH.cost μ ≤ WH.Gfn (γ - τγ) ∧
        WH.Gfn (γ - τγ) ≤ μ ⬝ᵥ (γ - τγ) - WH.cost μ + ε) := by
  obtain ⟨s, μ, φ, hs0, hφ, hPt, hTt, hμ0, hμA, hG, hH⟩ :=
    theorem3_limit (WG := WG) (WH := WH) (α := α) (γ := γ)
      hcG hDG hDH hDHconv hcostH_conv hA0
  refine ⟨s, μ, hs0, hμ0, hμA, hG, hH, ?_, ?_⟩
  · intro ε hε
    have hμD : μ ∈ WG.D := by
      obtain ⟨-, hD, -⟩ :=
        (WG.mem_rejectSet_iff_acceptance s.nonneg_Ainf).mp hG
      rwa [sub_sub_cancel] at hD
    have hoptG : WG.boxValue α s.Ainf = μ ⬝ᵥ α - WG.cost μ := by
      have h := WG.boxValue_eq_of_mem_rejectSet s.nonneg_Ainf hG
      rwa [sub_sub_cancel] at h
    obtain ⟨τ, hτ0, hFY, htight, -, hslε⟩ :=
      WG.exists_approx_kkt hDGconv hcostG_conv α s.nonneg_Ainf hμD hμA
        hoptG hε
    exact ⟨τ, hτ0, hFY, htight, hslε⟩
  · intro ε hε
    have hμD : μ ∈ WH.D := by
      obtain ⟨-, hD, -⟩ := (WH.mem_rejectSet_iff_acceptance hμ0).mp hH
      rwa [sub_zero] at hD
    have hoptH : WH.boxValue γ μ = μ ⬝ᵥ γ - WH.cost μ := by
      have h := WH.boxValue_eq_of_mem_rejectSet hμ0 hH
      rwa [sub_zero] at h
    obtain ⟨τ, hτ0, hFY, htight, -, -⟩ :=
      WH.exists_approx_kkt hDHconv hcostH_conv γ hμ0 hμD (le_refl μ)
        hoptH hε
    exact ⟨τ, hτ0, hFY, htight⟩

end GHS
