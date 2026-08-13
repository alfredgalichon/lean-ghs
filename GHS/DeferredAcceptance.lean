import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions
import Mathlib.Order.Monotone.Basic

/-!
# GHS Phase 6: deferred-acceptance availability dynamics (Theorem 3, skeleton)

The bookkeeping layer of GHS Algorithm 1 and the opening of the proof of
Theorem 3, abstracted from the optimization content: sequences of
availabilities `A`, proposals `P`, and tentative acceptances `T` linked by the
update rule `A (k+1) = A k - (P k - T k)` and the feasibility inequalities
`0 ≤ T k ≤ P k ≤ A k`.  Machine-checked here:

* `DASequences.antitone_A`, `nonneg_A` — availabilities decrease and stay
  nonnegative (the induction of Proposition 3's bookkeeping);
* `DASequences.tendsto_A` — availabilities converge (monotone convergence,
  coordinatewise);
* `DASequences.tendsto_sub_PT` — the rejected masses `P k - T k` vanish:
  the algorithm's stopping criterion is met in the limit.

The optimization content that feeds these hypotheses — the proposal/disposal
phases are well-defined and satisfy `T ≤ P ≤ A` along the iteration — is
Proposition 3, whose key monotonicity brick is
`GHS.exists_rejection_le_of_capacity_le` in `GHS/CapacityMCS.lean`.

Mathlib-only (part of the standalone `GHS` target).
-/

open Filter Topology

namespace GHS

/-- The availability/proposal/acceptance bookkeeping of Algorithm 1. -/
structure DASequences (ι : Type*) where
  /-- available masses at the start of round `k` -/
  A : ℕ → ι → ℝ
  /-- proposed masses in round `k` -/
  P : ℕ → ι → ℝ
  /-- tentatively accepted masses in round `k` -/
  T : ℕ → ι → ℝ
  nonneg_T : ∀ k, 0 ≤ T k
  T_le_P : ∀ k, T k ≤ P k
  P_le_A : ∀ k, P k ≤ A k
  update : ∀ k, A (k + 1) = A k - (P k - T k)

namespace DASequences

variable {ι : Type*} (s : DASequences ι)

theorem antitone_A : Antitone s.A := by
  refine antitone_nat_of_succ_le fun k => ?_
  rw [s.update k]
  intro i
  have h1 := s.T_le_P k i
  show s.A k i - (s.P k i - s.T k i) ≤ s.A k i
  linarith

theorem nonneg_A : ∀ k, 0 ≤ s.A k := by
  intro k
  cases k with
  | zero =>
    intro i
    have h1 : (0:ℝ) ≤ s.T 0 i := s.nonneg_T 0 i
    have h2 : s.T 0 i ≤ s.P 0 i := s.T_le_P 0 i
    have h3 : s.P 0 i ≤ s.A 0 i := s.P_le_A 0 i
    show (0:ℝ) ≤ s.A 0 i
    linarith
  | succ k =>
    rw [s.update k]
    intro i
    have h1 : (0:ℝ) ≤ s.T k i := s.nonneg_T k i
    have h2 : s.P k i ≤ s.A k i := s.P_le_A k i
    show (0:ℝ) ≤ s.A k i - (s.P k i - s.T k i)
    linarith

/-- The limiting availability vector. -/
noncomputable def Ainf : ι → ℝ := fun i => ⨅ k, s.A k i

theorem nonneg_Ainf : 0 ≤ s.Ainf := by
  intro i
  exact le_ciInf fun k => s.nonneg_A k i

theorem Ainf_le (k : ℕ) : s.Ainf ≤ s.A k := by
  intro i
  refine ciInf_le ⟨0, ?_⟩ k
  rintro x ⟨m, rfl⟩
  exact s.nonneg_A m i

/-- Availabilities converge (coordinatewise monotone convergence). -/
theorem tendsto_A : Tendsto s.A atTop (𝓝 s.Ainf) := by
  rw [tendsto_pi_nhds]
  intro i
  refine tendsto_atTop_ciInf (fun k l hkl => ?_) ⟨0, ?_⟩
  · exact s.antitone_A hkl i
  · rintro x ⟨k, rfl⟩
    exact s.nonneg_A k i

/-- The rejected masses vanish: `P k - T k → 0`. This is the convergence of
the stopping criterion of Algorithm 1. -/
theorem tendsto_sub_PT : Tendsto (fun k => s.P k - s.T k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => s.A (k + 1)) atTop (𝓝 s.Ainf) :=
    s.tendsto_A.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k => s.A k - s.A (k + 1)) atTop (𝓝 (s.Ainf - s.Ainf)) :=
    s.tendsto_A.sub h1
  rw [sub_self] at h2
  refine h2.congr fun k => ?_
  rw [s.update k]
  abel

/-- Proposals are trapped between the acceptances and the availabilities, so
along any subsequence where `T` converges, `P` converges to the same limit —
the form in which Theorem 3 extracts its converging subsequence. -/
theorem P_between (k : ℕ) : s.T k ≤ s.P k ∧ s.P k ≤ s.A k :=
  ⟨s.T_le_P k, s.P_le_A k⟩

/-- Proposals live in the compact box `[0, A 0]`. -/
theorem P_mem_box [Fintype ι] (k : ℕ) : s.P k ∈ Set.Icc 0 (s.A 0) := by
  constructor
  · exact le_trans (s.nonneg_T k) (s.T_le_P k)
  · exact le_trans (s.P_le_A k) (s.antitone_A (Nat.zero_le k))

/-- **Theorem 3, subsequence extraction (the `μ` part)**: some subsequence of
the proposals converges, and along it the tentative acceptances converge to
the same limit (their gap vanishes). -/
theorem exists_subseq_tendsto [Fintype ι] :
    ∃ μ ∈ Set.Icc 0 (s.A 0), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => s.P (φ k)) atTop (𝓝 μ) ∧
      Tendsto (fun k => s.T (φ k)) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ, φ, hφ, htend⟩ :=
    (isCompact_Icc (a := (0 : ι → ℝ)) (b := s.A 0)).tendsto_subseq s.P_mem_box
  refine ⟨μ, hμ, φ, hφ, htend, ?_⟩
  have hsub : Tendsto (fun k => s.P (φ k) - s.T (φ k)) atTop (𝓝 0) :=
    s.tendsto_sub_PT.comp hφ.tendsto_atTop
  have h := htend.sub hsub
  rw [sub_zero] at h
  refine h.congr fun k => ?_
  show s.P (φ k) - (s.P (φ k) - s.T (φ k)) = s.T (φ k)
  abel

end DASequences

end GHS
