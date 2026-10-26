import GHS.Theorem2

/-!
# S-convexity: the GHS corollary

Chen and Li's Theorem 2 is a substantial external input: the conjugate of a
lower-semicontinuous proper S-convex function is submodular and convex.  This
file formalizes the S-exchange premise and machine-checks the exact remaining
implication from their conjugate-submodularity conclusion to exchangeability.
-/

open Set

namespace GHS

variable {n : ℕ}

/-- The coordinate direction `e_i - β e_j`, with `none` representing the
dummy index `j = 0` and hence `e_0 = 0`. -/
def sExchangeDirection (i : Fin n) (j : Option (Fin n)) (β : ℝ) :
    Fin n → ℝ :=
  Pi.single i (1 : ℝ) - β • (match j with
    | none => (0 : Fin n → ℝ)
    | some k => Pi.single k (1 : ℝ))

/-- The local exchange property `(S-EXC)` of Chen and Li.  Finiteness is
expressed by membership in the effective domain.  The option `none` is their
index `0`, for which no compensating coordinate is used. -/
def SExchange (c : (Fin n → ℝ) → EReal) : Prop :=
  ∀ x y : Fin n → ℝ, c x ≠ ⊤ → c y ≠ ⊤ →
    ∀ i : Fin n, y i < x i →
      ∃ j : Option (Fin n),
        (match j with
          | none => True
          | some k => x k < y k) ∧
        ∃ α0 β : ℝ, 0 < α0 ∧ 0 < β ∧
          ∀ α ∈ Icc (0 : ℝ) α0,
            c (x - α • sExchangeDirection i j β) +
                c (y + α • sExchangeDirection i j β) ≤ c x + c y

/-- The full premise of GHS Proposition 2.4: lower semicontinuity,
proper convexity, and the Chen--Li S-exchange property. -/
structure ProperLscSConvex (c : (Fin n → ℝ) → EReal) : Prop where
  lowerSemicontinuous : LowerSemicontinuous c
  properConvex : ProperConvexFunctionOn Set.univ c
  sExchange : SExchange c

/-- The GHS step after applying Chen--Li Theorem 2: submodularity of the
conjugate implies exchangeability. -/
theorem exchangeable_of_sConvex_conjugate_submodular
    {c : (Fin n → ℝ) → EReal}
    (hc : ProperLscSConvex c)
    (hsub : POrderE (fenchelConjugate n c) (fenchelConjugate n c)) :
    QOrderE c c :=
  (qOrderE_self_iff_pOrderE_fenchelConjugate_self
    hc.lowerSemicontinuous hc.properConvex).2 hsub

/-- Explicit literature-interface form of GHS Proposition 2.4.  The premise
`hCL` is exactly the conjugate-submodularity conclusion supplied by Chen and
Li's Theorem 2.  The remaining deduction to exchangeability is checked here. -/
theorem exchangeable_of_sConvex_via_chenLi
    {c : (Fin n → ℝ) → EReal}
    (hc : ProperLscSConvex c)
    (hCL : ProperLscSConvex c →
      POrderE (fenchelConjugate n c) (fenchelConjugate n c)) :
    QOrderE c c :=
  exchangeable_of_sConvex_conjugate_submodular hc (hCL hc)

end GHS
