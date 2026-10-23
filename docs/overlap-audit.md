# Dependency overlap and private inspection scope

Source audit date: 2026-10-22; pinned-source extension review: 2026-10-23. This is a private standalone packaging candidate, not a claim of
new mathematics, exclusive formalization, upstream readiness, or Mathlib acceptance.

The actual [MCMC TotalVariation source](https://github.com/or4nge19/MCMC/blob/b874137741fbdf23eaac83540b9f79a912a2bc0d/MCMC/Finite/TotalVariation.lean)
already defines finite TV and a row Dobrushin coefficient, with `tvDist_contract`,
`dobrushinCoeff_mul` and `dobrushinCoeff_pow`. Its
[convergence source](https://github.com/or4nge19/MCMC/blob/b874137741fbdf23eaac83540b9f79a912a2bc0d/MCMC/Finite/Convergence.lean)
also develops mixing consequences. This is substantial mathematical/API overlap; ordinary finite
TV contraction and powers must not be advertised as new. The comparison read actual theorem
signatures, including matrix and stochasticity hypotheses, rather than relying on its README.
No external MCMC build or proof audit was performed here.

The present package uses typed probability vectors and rectangular kernels, an operator/row
coefficient identity, unconditional finite stationary existence, block estimates, perturbation
bounds, exact binary identities, and PMF/measure adapters. These describe this API, not established novelty over MCMC.
An upstream proposal would first need a theorem-by-theorem translation and an agreed API delta.

Current [Mathlib total variation](https://github.com/leanprover-community/mathlib4/blob/6ea173996caaa665b0a3c4f81ce472e04e4f7754/Mathlib/MeasureTheory/Measure/TotalVariation/Basic.lean)
and its probability-kernel infrastructure supply neighboring foundations. The audited current
Mathlib tree contained no filename with Dobrushin, but filename absence is not a proof that an
equivalent theorem is absent. No Mathlib acceptance or exhaustive ecosystem search is claimed.
The native compatibility checks use the separately pinned d13f23b/Lean4.34.1 pair, not this newer
current Mathlib commit.

## Pinned-source integration additions

At the supported d13f23b revision, Mathlib's
[`SignedMeasure.totalVariation_eq_variation`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/MeasureTheory/VectorMeasure/Variation/SignedMeasure.lean)
and `VectorMeasure.variation_apply_singleton` reduce the finite bridge to singleton masses.
The resulting total variation **measure** has mass `2 * TV(p, q)`; it is not the half-L1
probability-distance convention. The new bridge formally proves this normalization.

The same pinned tree's `LinearAlgebra/Matrix/Stochastic.lean` defines stochastic matrices and
basic algebraic API; it does not itself provide a stationary probability-law existence result.
The package's finite existence proof instead uses compactness of the coordinate cube and
[`tendsto_birkhoffAverage_apply_sub_birkhoffAverage'`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Dynamics/BirkhoffSum/NormedSpace.lean).
This is an integration and completeness improvement to the finite-law API. It does not establish
priority or novelty over other formalizations, including the external MCMC sources above.
