import GHS.Theorem2

/-!
# Continuous M-natural convexity: the GHS corollary

Murota and Shioura's continuous conjugacy theorem is a substantial external
input: the conjugate of a closed proper continuous M-natural-convex function
is continuous L-natural-convex.  This file does not reprove that literature
result.  Instead, it records its two consequences used in GHS, ordinary
submodularity of the conjugate and common-shift increasing differences, and
machine-checks the exact remaining implication to exchangeability.
-/

namespace GHS

variable {n : ℕ}

/-- Increasing differences between the price vector and a common scalar
shift.  This is the additional dual restriction discussed in GHS Section
2.3.4; it is not needed for exchangeability. -/
def CommonShiftIncreasingDifferences
    (g : (Fin n → ℝ) → EReal) : Prop :=
  ∀ p p' : Fin n → ℝ, ∀ t t' : ℝ, p ≤ p' → t ≤ t' →
    g (p + t' • (1 : Fin n → ℝ)) + g (p' + t • (1 : Fin n → ℝ)) ≤
      g (p + t • (1 : Fin n → ℝ)) + g (p' + t' • (1 : Fin n → ℝ))

/-- The two consequences of continuous L-natural convexity invoked in the
paper.  Murota--Shioura conjugacy supplies this data for the conjugate of a
continuous M-natural-convex function. -/
structure ContinuousLNaturalConsequences
    (g : (Fin n → ℝ) → EReal) : Prop where
  submodular : POrderE g g
  commonShiftIncreasingDifferences : CommonShiftIncreasingDifferences g

/-- The part of the continuous M-natural-convexity implication proved inside
GHS: once the published conjugacy theorem supplies L-natural consequences for
the conjugate, GHS conjugate duality yields exchangeability. -/
theorem exchangeable_of_continuousLNatural_conjugate
    {c : (Fin n → ℝ) → EReal}
    (hc_lsc : LowerSemicontinuous c)
    (hc : ProperConvexFunctionOn Set.univ c)
    (hdual : ContinuousLNaturalConsequences (fenchelConjugate n c)) :
    QOrderE c c :=
  (qOrderE_self_iff_pOrderE_fenchelConjugate_self hc_lsc hc).2
    hdual.submodular

/-- Explicit literature-interface form of GHS Proposition 2.4.  The predicate
`IsContinuousMNatural` fixes the chosen formal definition of continuous
M-natural convexity, while `hMS` is precisely the Murota--Shioura conjugacy
input.  Thus the theorem checks the GHS corollary without treating the cited
conjugacy theorem as if it had been reproved here. -/
theorem exchangeable_of_continuousMNatural_via_murotaShioura
    (IsContinuousMNatural : ((Fin n → ℝ) → EReal) → Prop)
    {c : (Fin n → ℝ) → EReal}
    (hc_lsc : LowerSemicontinuous c)
    (hc : ProperConvexFunctionOn Set.univ c)
    (hcM : IsContinuousMNatural c)
    (hMS : IsContinuousMNatural c →
      ContinuousLNaturalConsequences (fenchelConjugate n c)) :
    QOrderE c c :=
  exchangeable_of_continuousLNatural_conjugate hc_lsc hc (hMS hcM)

end GHS
