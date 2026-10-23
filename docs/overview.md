# Finite Markov-kernel contraction and mixing

Finite probability vectors admit zero coordinates. Finite kernels act on them by matrix
multiplication, with total variation normalized as one half of the L1 distance.

The library proves stationary-law existence for every kernel on a nonempty finite state space,
the operator/row-diameter Dobrushin coefficient identity, submultiplicativity, finite-block
contraction bounds, uniqueness and attraction, and finite-time/stationary perturbation estimates.
Binary-input kernels have an exact scaling identity; binary endomorphisms have an exact geometric
law. The PMF adapter connects these objects to Mathlib PMF and probability kernels.

The existence theorem in `StationaryExistence` is exposed as
`FiniteMarkovKernel.exists_isStationary`. Its proof forms Cesàro averages of an arbitrary orbit,
extracts a convergent subsequence from the compact coordinate cube, and uses Mathlib's bounded
Birkhoff-average shift limit to prove stationarity. Finite nonemptiness is explicit; no supplied
stationary law or strict positivity assumption enters this theorem.

`MeasureTotalVariation` identifies the finite distance with one half of the total mass of
Mathlib's `SignedMeasure.totalVariation` for the difference of the encoded probability measures.
The theorem `ProbabilityVector.signedMeasure_totalVariation_univ` states the factor in the other
direction. Measurable singleton assumptions ensure the finite encodings retain all coordinates.

Existence alone gives neither uniqueness nor mixing. Strict block contraction remains an explicit
hypothesis for uniqueness and quantitative decay. Binary formulas remain binary results.

## Organization

- `ProbabilityVector`: closed finite simplex, support and relabeling operations.
- `MarkovKernelContraction`: total variation, application, composition and operator coefficient.
- `DobrushinCoefficient`: row-diameter coefficient and its equality with the operator coefficient.
- `BlockErgodicity`: uniqueness and attraction under a supplied strict temporal block.
- `KernelPerturbation`: finite-time and stationary-law stability estimates.
- `BinaryKernelContraction`: exact binary finite-lag scaling and asymptotic decay.
- `PMFAdapter`: PMF/kernel interoperability.
- `StationaryExistence`: unconditional finite existence and strict-contraction uniqueness.
- `MeasureTotalVariation`: the factor-two bridge to Mathlib signed-measure variation.

The top-level import exports the mathematical modules. `FiniteMarkovKernelsExamples` is a separate
library target: it is built by the default build but is not imported by the public
root. Every source has a module description and documented public declarations.
The only external package requirement is pinned Mathlib and its public dependencies.

## Qualification contract

A fresh authored-artifact build must pass with warnings fatal. Full lint recompiles
the original source contents under the same module identity, rather than linting
only an import of cached declarations. All explicit public declaration names are
listed in `verification.json`, checked against the source and audited transitively.
Private/generated declarations are not individually listed; the public audit follows
their transitive use. The lexical custom-axiom and proof-hole screen is an additional
source check, not a substitute for the transitive audit.

The CI workflow runs the same verification program with immutable action references
and read-only repository permissions. It contains no release, Pages deployment,
automatic dependency update or publishing step. A workflow definition is not a hosted
execution receipt.

## Packaging benchmark

The comparison used actual checked-out versions of the author's five public libraries:

- `cencov-petz` at `f6cf035a4c2882ae1fbc0a83416ab8142aceb676` (leanprover/lean4:v4.29.1).
- `channel-capacity` at `fdb4d1d18dba3e408fbe1969e09a4da3da2e313e` (leanprover/lean4:v4.29.1).
- `compact-spectral` at `72cd62dbdd4c397d26fc0c5777d60fea2211e938` (leanprover/lean4:v4.29.1).
- `godel-loeb` at `60a7a1098c34dbd0ee0833dde94ef5315f22d472` (leanprover/lean4:v4.29.1).
- `rellich-kondrachov` at `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` (leanprover/lean4:v4.29.1).

The baseline practices retained here are a small public root, Mathlib-only dependencies,
explicit mathematical scope, per-file authorship/license notices and usage documentation.
The additional gates are built examples, immutable Mathlib/action revisions, explicit
warning-fatal source/full-lint execution and a complete named public axiom ledger.
This compares observable packaging and verification practice; it does not assert that
one library's mathematics is superior to another's or that the older projects failed.

## Refreshed comparison, 2026-10-22

All five precedent remote heads were rechecked and equal the commits listed above. This is an
audit of actual source/configuration, not an inference that every earlier project ran every
present check. All five lock nine public dependencies and pin Lean4.29.1. Cencov-Petz,
compact-spectral and Rellich-Kondrachov use Lean lakefiles and retain root LICENSE files;
channel-capacity and godel-loeb use TOML lakefiles and retain root `LICENSE-APACHE` and
`LICENSE-MIT` texts; their READMEs specify dual MIT OR Apache 2.0 licensing. Authored file
notices and repository license declarations must be read together.
Channel-capacity has concrete positive/counterexample modules; the other projects have their own
scoped APIs, source checks and documentation rather than the same example layout.

This package keeps a small public root, opt-in example imports, Mathlib-only dependencies,
per-file Apache notices and ORIGIN hashes. Its additional implemented gates are exact-source
builds, all16 source linters, the explicit transitive axiom ledger, durable verifier rejection
controls and always-retained CI evidence configuration. No precedent was modified or requalified.
The supported pair remains Lean4.34.1/d13f23b; earlier-pair compatibility is not inferred.

## Readiness additions, 2026-10-23

The mathematical additions are stationary existence and the explicit measure-variation bridge.
The README now leads with theorem hypotheses, formulas, and checked consumer examples; qualification
process detail remains here. The locked Lean/Mathlib pair and public-dependency policy are unchanged.
Historical receipts under `docs/qualification*` and `docs/private-release*` refer to their recorded
source identities; they do not qualify later source edits. Current verification records are emitted
by `python3 scripts/verify.py` and retained separately for the exact checked source tree.

## Mathematical readiness qualification

The [October 23 source qualification](readiness-qualification.json) records unconditional
finite stationary existence, the Mathlib variation bridge, their consumers and current
source hashes. Earlier receipts remain historical. Hosted CI and final-candidate review
are separate results.
