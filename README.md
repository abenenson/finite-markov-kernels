# finite-markov-kernels

[![Lean verification](https://github.com/abenenson/finite-markov-kernels/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/abenenson/finite-markov-kernels/actions/workflows/lean.yml)

Finite Markov kernels, stationary laws, and quantitative mixing in Lean and Mathlib.
Probability vectors may have zero coordinates. Kernels may be rectangular; stationary
laws concern endomorphisms on a **nonempty finite** state space.

The public API proves:

- **Finite disintegration:** given a fallback probability row on each fiber, a dependent joint
  law reconstructs exactly from its first marginal and conditional rows. The fallback supplies
  conditionals on zero-mass fibers; it has no effect on the reconstructed joint law.
- **Stationary existence:** every finite endomorphism has a probability vector `π` with
  `K.apply π = π`. The proof uses compactness and Cesàro averages; it needs no positivity,
  irreducibility, or contraction assumption.
- **Dobrushin identity:** for a nonempty input alphabet, the operator contraction coefficient
  equals the maximum TV distance between rows. Coefficients are submultiplicative under
  composition and powers.
- **Uniqueness and mixing:** a coefficient strictly below one at any finite block gives a
  unique stationary law. For every stationary `π`,
  `TV((K.iterate n).apply p, π) ≤ δ(K)^n * TV(p, π)`, with corresponding block bounds.
- **Mathlib integration:** finite laws and rows roundtrip through `PMF` and probability
  kernels. Mathlib's signed-measure variation mass of `μ - ν` is **twice** this library's
  `TV(p, q) = (1/2) * ∑ a, |p a - q a|`.
- **Further bounds:** finite-time and stationary perturbation estimates, plus exact binary
  contraction formulas and geometric rates.

## Use

```lean
import FiniteMarkovKernels

open FiniteMarkovKernels

example {A : Type*} [Fintype A] [Nonempty A] (K : FiniteMarkovKernel A A) :
    ∃ π : ProbabilityVector A, K.IsStationary π :=
  K.exists_isStationary

example {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (K : FiniteMarkovKernel A A) (block : ℕ)
    (h : FiniteMarkovKernel.contractionCoefficient (K.iterate block) < 1) :
    ∃! π : ProbabilityVector A, K.IsStationary π :=
  K.existsUnique_isStationary_of_iterate_contractionCoefficient_lt_one block h

example {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (p q : ProbabilityVector A) :
    ((p.toPMF.toMeasure.toSignedMeasure - q.toPMF.toMeasure.toSignedMeasure).totalVariation
      Set.univ).toReal = 2 * ProbabilityVector.totalVariation p q :=
  p.signedMeasure_totalVariation_univ q
```

[Checked examples](FiniteMarkovKernelsExamples/Basic.lean) include a binary channel with
flip probability `1/4`, exact rate `1/2`, a fair stationary law, the measure-variation
normalization, and generic existence-to-attraction and row-coefficient-to-uniqueness proofs.
The [disintegration example](FiniteMarkovKernelsExamples/Disintegration.lean) checks exact
joint-law reconstruction with distinct choices on a zero-mass conditional fiber.
Import `FiniteMarkovKernelsExamples` to use them.

## Build

Pinned and tested: **Lean 4.34.1**, **Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`**. Transitive dependencies are locked in
[lake-manifest.json](lake-manifest.json).

```bash
lake exe cache get
lake --rehash --wfail build
python3 scripts/verify.py
```

The verifier checks every source and example with all 16 linters, warnings fatal,
public declaration coverage, and transitive axioms restricted to `Classical.choice`,
`Quot.sound`, and `propext`. See [API and verification notes](docs/overview.md) for the
module map and qualification evidence.

Existence alone implies neither uniqueness nor convergence; the quantitative bounds retain
explicit contraction hypotheses. Exact binary identities apply to binary alphabets.
Related finite TV contraction and mixing formalizations already exist; see the
[source overlap comparison](docs/overlap-audit.md) for scope and attribution.

Apache 2.0. Copyright 2026 Adam Benenson. See [LICENSE](LICENSE), [NOTICE](NOTICE), and
[initial public file inventory](ORIGIN.json). Local verification and hosted CI execution are
distinct results.
