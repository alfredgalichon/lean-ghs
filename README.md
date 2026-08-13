# lean-ghs

Lean 4 / Mathlib machine verification of

> **A. Galichon, Y.-W. Hsieh, M. Sylvestre**,
> *Monotone comparative statics for submodular functions, with an application
> to aggregated deferred acceptance* (submitted, 2025).

Author of the formalization: Alfred Galichon (New York University).
The development is **Mathlib-only** (no external dependencies beyond the
pinned Mathlib commit) and contains no `sorry` and no extra axioms.

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
- `GHS/Orders.lean` — Q-/P-orders on functions and sets (values in
  `WithTop R`), exchangeability, submodularity, matrons, sublattices, the
  `(epsilon, D)`-refinements.
- `GHS/BoxCalculus.lean`, `GHS/Topkis.lean`, `GHS/WeakSetOrder.lean`,
  `GHS/ExchangeableConvex.lean` — box calculus, Topkis and dual Topkis
  (Claim 3 / Theorem 1), Q-order implies weak set order (Proposition 2, with
  the nonemptiness correction), the midpoint form of Proposition 1.

**The conjugacy core (Theorem 4 / Claim 1 / Corollary 1)**
- `GHS/Rockafellar.lean` — a standalone finite-dimensional convex-duality
  layer: subgradient existence, affine minorants, Fenchel-Moreau
  biconjugation, conjugates closed convex proper.
- `GHS/Conjugacy.lean`, `GHS/ConjugacyDual.lean`, `GHS/PaschHausdorff.lean`,
  `GHS/Theorem4.lean` — `f <=_Q g  iff  g* <=_P f*` for closed proper convex
  functions, in both directions, with the epsilon-forms and the
  support-function Corollary 1. The forward direction is proved sharper than
  stated (no convexity or closedness needed).

**Theorem 2, the full cycle**
- `GHS/Theorem2.lean` — (1) iff (2): exchangeable iff submodular conjugate.
- `GHS/CapacityMCS.lean`, `GHS/PriceMCS.lean` — (1) implies (4), jointly in
  price and capacity, with the D-restricted dual Topkis.
- `GHS/SubdiffOrder.lean`, `GHS/SubdiffMCS.lean` — (4) implies (3) and
  (3) implies (2) (finite-valued conjugates), closing
  `(1) => (4) => (3) => (2) => (1)`.
- `GHS/Stieltjes.lean`, `GHS/QuadraticExample.lean`,
  `GHS/EntropyExample.lean` — the Stieltjes characterization (sharper: no
  symmetry needed), Example 2 (quadratic cost exchangeable iff the inverse
  matrix has nonpositive off-diagonals), and the corrected Example 1.

**The matching side (Lemmas 1-3, Proposition 3, Theorem 3)**
- `GHS/WelfareData.lean`, `GHS/Proposition3.lean`,
  `GHS/DeferredAcceptance.lean` — the welfare bundles, Lemma 1, the
  well-definedness of Algorithm 1, and its bookkeeping dynamics.
- `GHS/OrthantDuality.lean`, `GHS/Equilibrium.lean` — Lemma 2 (Kuhn-Tucker)
  via orthant strong duality in epsilon-form at finite waiting times, and the
  epsilon-equilibrium form of Theorem 3.
- `GHS/TauCompact.lean` — the exact compactified layer: waiting times in
  `[0, infinity]` with the convention `0 * infinity = 0`, exact attainment,
  strong duality and Kuhn-Tucker, Lemma 3 (monotone least waiting times),
  and Theorem 3 in its full corrected exact form, including the
  `min(tau_alpha, tau_gamma) = 0` normalization with the paper's implicit
  standing assumptions made explicit.

**Examples**
- `GHS/RandomUtility.lean` — the finite-support random-utility welfare is
  submodular.
- `GHS/CappedLogit.lean` — the capped-logit water-filling equation is well
  posed.

## Provenance

This repository is a pushed snapshot of the `GHS` library of a private
monorepo (`self-lectures`), which is the source of truth; it is re-staged
manually and carries no history of the monorepo.
