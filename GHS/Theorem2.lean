import GHS.Theorem4

/-!
# GHS Theorem 2, items (1) ⟺ (2): exchangeable ⟺ submodular conjugate

The self-pair specialization of Theorem 4 / Claim 1
(`GHS.qOrderE_iff_pOrderE_fenchelConjugate`): a closed proper convex cost
`c` is **exchangeable** (Q-ordered against itself) iff its Fenchel conjugate
`c*` is **submodular** (P-ordered against itself).

Two forms:

* `qOrderE_self_iff_pOrderE_fenchelConjugate_self` — `EReal`-valued, the
  ambient vocabulary of the conjugacy chain;
* `exchangeable_iff_pOrderE_fenchelConjugate` — the paper's `ℝ ∪ {+∞}`
  vocabulary (`ERealTop`-valued `c`, `GHS.Exchangeable` from `GHS/Orders.lean`),
  transported through the `toE` bridge.

The remaining items of Theorem 2 — the price- and capacity-induced monotone
comparative statics — are covered (at fixed `p`, resp. in unprojected form) by
`GHS.qOrderSet_capacity` in `GHS/CapacityMCS.lean`; the projected `(ε, D)`
forms are deferred (see the roadmap).

Mathlib-only (via the standalone `GHS.Rockafellar` layer).
-/

namespace GHS

variable {n : ℕ}

/-- **GHS Theorem 2, (1) ⟺ (2), `EReal` form.** For closed proper convex `c`
on `ℝⁿ`: `c` is exchangeable iff `c*` is submodular. -/
theorem qOrderE_self_iff_pOrderE_fenchelConjugate_self
    {c : (Fin n → ℝ) → EReal}
    (hc_lsc : LowerSemicontinuous c) (hc : ProperConvexFunctionOn Set.univ c) :
    QOrderE c c ↔ POrderE (fenchelConjugate n c) (fenchelConjugate n c) :=
  qOrderE_iff_pOrderE_fenchelConjugate hc_lsc hc hc_lsc hc

/-- **GHS Theorem 2, (1) ⟺ (2), paper form.** For `c : ℝⁿ → ℝ ∪ {+∞}`
closed proper convex (hypotheses stated through the `toE` embedding into
`EReal`): `c` is exchangeable iff its Fenchel conjugate is submodular. -/
theorem exchangeable_iff_pOrderE_fenchelConjugate
    {c : (Fin n → ℝ) → ERealTop}
    (hc_lsc : LowerSemicontinuous fun q => toE (c q))
    (hc : ProperConvexFunctionOn Set.univ fun q => toE (c q)) :
    Exchangeable c ↔
      POrderE (fenchelConjugate n fun q => toE (c q))
        (fenchelConjugate n fun q => toE (c q)) :=
  qOrderE_toE_iff.symm.trans
    (qOrderE_iff_pOrderE_fenchelConjugate hc_lsc hc hc_lsc hc)

end GHS
