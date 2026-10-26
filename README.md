# lean-ghs

Lean 4 / Mathlib machine verification of

> **A. Galichon, Y.-W. Hsieh, M. Sylvestre**,
> *Monotone comparative statics under dual submodularity, with an application
> to aggregate deferred acceptance* (revised version, 2026).

Author of the formalization: Alfred Galichon (New York University).
The development is **Mathlib-only** (no external dependencies beyond the
pinned Mathlib commit), contains no `sorry`, and invokes no axioms beyond
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Building

```
lake exe cache get   # download the Mathlib build cache
lake build GHS
```

The `lean-toolchain` file and the Mathlib `rev` in `lakefile.toml` are pinned
to each other.

## What is verified

All of the paper's results, with several statements sharpened and several
proof gaps repaired (the repairs are catalogued in the companion errata note
of the `self-lectures` development).

**Vocabulary and elementary theory**
- `GHS/Orders.lean`: Q-/P-orders on functions and sets (values in
  `WithTop R`), exchangeability, submodularity, matrons, sublattices, the
  `(epsilon, D)`-refinements.
- `GHS/BoxCalculus.lean`, `GHS/Topkis.lean`, `GHS/WeakSetOrder.lean`,
  `GHS/ExchangeableConvex.lean`: box calculus, Topkis and dual Topkis
  (Claim 3 / Theorem 1), Q-order implies weak set order (Proposition 2, with
  the nonemptiness correction), the midpoint form of Proposition 1.

**The conjugacy core (Theorem 4 / Claim 1 / Corollary 1)**
- `ConvexAnalysis/FiniteDimensional.lean`: reusable finite-dimensional
  convex-duality infrastructure.
- `GHS/Rockafellar.lean`: the GHS-facing finite-dimensional convex-duality
  layer: subgradient existence, affine minorants, Fenchel-Moreau
  biconjugation, conjugates closed convex proper.
- `GHS/Conjugacy.lean`, `GHS/ConjugacyDual.lean`, `GHS/PaschHausdorff.lean`,
  `GHS/Theorem4.lean`: `f <=_Q g  iff  g* <=_P f*` for closed proper convex
  functions, in both directions, with the epsilon-forms and the
  support-function Corollary 1. The forward direction is proved sharper than
  stated (no convexity or closedness needed).

**Theorem 2, the full cycle**
- `GHS/Theorem2.lean`: (1) iff (2), exchangeable iff submodular conjugate.
- `GHS/CapacityMCS.lean`, `GHS/PriceMCS.lean`: (1) implies (4), jointly in
  price and capacity, with the D-restricted dual Topkis.
- `GHS/SubdiffOrder.lean`, `GHS/SubdiffMCS.lean`: (4) implies (3) and
  (3) implies (2) (finite-valued conjugates), closing
  `(1) => (4) => (3) => (2) => (1)`.
- `GHS/ExtendedDomainMCS.lean`, `GHS/ExtendedFenchel.lean`,
  `GHS/ExtendedFenchelRejections.lean`, `GHS/ExtendedRejectionOrder.lean`,
  `GHS/ExtendedRejectionMCS.lean`, and `GHS/ExtendedTheorem2.lean`: the full
  extended-valued converse on a sublattice effective domain.
- `GHS/ContinuousMNaturalCorollary.lean` and `GHS/SConvexCorollary.lean`:
  the implications from the cited continuous M-natural-convexity and
  S-convexity results to exchangeability.
- `GHS/Stieltjes.lean`, `GHS/QuadraticExample.lean`,
  `GHS/EntropyExample.lean`: the Stieltjes characterization (sharper: no
  symmetry needed), Example 2 (quadratic cost exchangeable iff the inverse
  matrix has nonpositive off-diagonals), and the corrected Example 1.

**The matching side (Lemmas 1-3, Proposition 3, Theorem 3)**
- `GHS/ClassicalStableBinary.lean`: the revised one-to-one stable NTU
  definition, its binary incidence-vector representation, Proposition 3.1,
  and Corollary 3.1, pointwise for the same matching.
- `GHS/DeterministicWelfare.lean`: submodularity of deterministic aggregate
  welfare and the finite-choice identity `C^G(U) = partial G(U)`.
- `GHS/WelfareData.lean`, `GHS/Proposition3.lean`,
  `GHS/DeferredAcceptance.lean`: the welfare bundles, Lemma 1, the
  well-definedness of Algorithm 1, and its bookkeeping dynamics.
- `GHS/OrthantDuality.lean`, `GHS/Equilibrium.lean`: Lemma 2 (Kuhn-Tucker)
  via orthant strong duality in epsilon-form at finite waiting times, and the
  epsilon-equilibrium form of Theorem 3.
- `GHS/TauCompact.lean` and `GHS/ExtendedWelfareContinuity.lean`: the exact
  compactified layer, including the canonical continuous welfare extension,
  waiting times in
  `[0, infinity]` with the convention `0 * infinity = 0`, exact attainment,
  strong duality and Kuhn-Tucker, Lemma 3 (monotone least waiting times),
  and Theorem 3 in its full corrected exact form, including the
  `min(tau_alpha, tau_gamma) = 0` normalization with the paper's implicit
  standing assumptions made explicit.

**Examples**
- `GHS/RandomUtility.lean`: general finite-measure random-utility welfare is
  submodular.
- `GHS/CappedLogit.lean`: the capped-logit water-filling equation is well
  posed.

## Provenance

This repository is a source-only snapshot of the `GHS` modules used in the
paper, together with their `ConvexAnalysis` and minimal `UGS` source
dependencies. The source is maintained in the canonical `self-lectures`
development. It contains no generated build artifacts.
