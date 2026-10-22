# Dependency overlap and private inspection scope

Source audit date: 2026-10-22. This is a private standalone packaging candidate, not a claim of
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
coefficient identity, supplied-stationary block estimates, perturbation bounds, exact binary
identities and a PMF adapter. These describe this API, not established novelty over MCMC.
An upstream proposal would first need a theorem-by-theorem translation and an agreed API delta.

Current [Mathlib total variation](https://github.com/leanprover-community/mathlib4/blob/6ea173996caaa665b0a3c4f81ce472e04e4f7754/Mathlib/MeasureTheory/Measure/TotalVariation/Basic.lean)
and its probability-kernel infrastructure supply neighboring foundations. The audited current
Mathlib tree contained no filename with Dobrushin, but filename absence is not a proof that an
equivalent theorem is absent. No Mathlib acceptance or exhaustive ecosystem search is claimed.
The native compatibility checks use the separately pinned d13f23b/Lean4.34.1 pair, not this newer
current Mathlib commit.
