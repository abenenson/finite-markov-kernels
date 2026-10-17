# finite-markov-kernels

Finite Markov-kernel contraction and mixing, formalized in Lean with Mathlib only.

Private preparation. Local qualification and its exact source identities are recorded
in `docs/qualification.json` when complete. Hosted CI execution is a separate result;
no hosted pass or public release is claimed.

## Mathematical scope

Finite probability vectors admit zero coordinates. Finite kernels act on them by matrix
multiplication, with total variation normalized as one half of the L1 distance.

The library proves the operator/row-diameter Dobrushin coefficient identity,
submultiplicativity, finite-block contraction bounds, uniqueness and attraction toward
a supplied stationary law, and finite-time/stationary perturbation estimates. Binary-input
kernels have an exact scaling identity; binary endomorphisms have an exact geometric law.
The PMF adapter connects these objects to Mathlib PMF and probability kernels.

Stationary-law existence is not claimed: the stationary laws in those bounds are supplied
and their stationarity is a theorem hypothesis. Strict block contraction is also explicit.
Binary exact formulas are binary results, not assertions for arbitrary alphabets.

## Build and verification

The supported tested pair is Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Every transitive dependency is locked in
`lake-manifest.json`. The author's earlier libraries currently pin Lean 4.29.1;
compatibility with that older pair has not been tested or claimed here.

```bash
lake exe cache get
lake --rehash --wfail build
python3 scripts/verify.py
```

The verifier forces every authored module and example to rebuild, re-elaborates
each source with all 16 linters including theorem documentation, rejects warnings,
checks declaration coverage, and audits transitive axioms of every explicit public
name. Only `Classical.choice`, `Quot.sound` and `propext` are allowed. It rejects
`sorry`, `admit`, explicit custom axioms and imports outside this package/Mathlib.
Logs and receipts go into a new `verification-artifacts` directory per run; failures
are retained. It uses Python's standard library and no private verification tooling.

## Usage

```lean
import FiniteMarkovKernels
-- Examples are opt-in:
import FiniteMarkovKernelsExamples
```

## Modules

- `ProbabilityVector`: closed finite simplex, support and relabeling operations.
- `MarkovKernelContraction`: total variation, application, composition and operator coefficient.
- `DobrushinCoefficient`: row-diameter coefficient and its equality with the operator coefficient.
- `BlockErgodicity`: uniqueness and attraction under a supplied strict temporal block.
- `KernelPerturbation`: finite-time and stationary-law stability estimates.
- `BinaryKernelContraction`: exact binary finite-lag scaling and asymptotic decay.
- `PMFAdapter`: PMF/kernel interoperability.

## Checked example

`FiniteMarkovKernelsExamples.Basic` builds a channel that flips a Boolean input with probability 1/4,
proves its row separation is 1/2, derives the exact finite-lag contraction formula,
checks its fair stationary law and PMF roundtrip, and proves the identity channel
retains full distinction at every lag.

## Provenance and license

Copyright 2026 Adam Benenson. Apache 2.0, matching the explicit notices retained in
the extracted mathematical files. See [LICENSE](LICENSE), [NOTICE](NOTICE), and
[ORIGIN.json](ORIGIN.json) for file identities and the limited extraction provenance.
No surrounding repository or unrelated source is assigned a license here.

[API and verification notes](docs/overview.md) describe the package boundary and
qualification process. These are formalizations of the scoped mathematical results;
no application-specific physical or empirical implication is claimed.
