/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovKernels

/-!
# A noisy binary kernel and its nonmixing control

Exact geometric contraction, an explicit stationary law, and PMF interoperability.
-/

namespace FiniteMarkovKernels.Examples

open FiniteMarkovKernel ProbabilityVector

/-- A binary channel that flips its input with probability one quarter. -/
noncomputable def binaryNoise : FiniteMarkovKernel Bool Bool :=
  fun bit ↦ boolBinary (if bit then 1 / 4 else 3 / 4) (by split_ifs <;> norm_num)

/-- The two rows are separated by exactly one half in total variation. -/
theorem binaryNoise_row_separation :
    totalVariation (binaryNoise false) (binaryNoise true) = 1 / 2 := by
  rw [totalVariation_bool]
  norm_num [binaryNoise, boolBinary_false]

/-- Every pair of initial laws contracts by exactly one half per time step. -/
theorem binaryNoise_exact_rate (steps : ℕ) (p q : ProbabilityVector Bool) :
    totalVariation ((iterate binaryNoise steps).apply p)
        ((iterate binaryNoise steps).apply q) =
      (1 / 2 : ℝ) ^ steps * totalVariation p q := by
  simpa only [binaryNoise_row_separation] using
    totalVariation_iterate_bool_eq_rowSeparation_pow_mul binaryNoise steps p q

/-- The fair binary law is stationary for the noisy channel. -/
theorem binaryNoise_fair_stationary :
    binaryNoise.IsStationary (boolBinary (1 / 2) (by norm_num)) := by
  apply ProbabilityVector.ext
  intro bit
  cases bit <;>
    norm_num [IsStationary, apply_prob, Fintype.sum_bool, binaryNoise,
      boolBinary_false, boolBinary_true]

/-- The identity channel retains the full distinction at every lag; strict contraction matters. -/
theorem identity_retains_distinction (steps : ℕ) :
    totalVariation ((iterate (identity : FiniteMarkovKernel Bool Bool) steps).apply
        (dirac false))
      ((iterate (identity : FiniteMarkovKernel Bool Bool) steps).apply (dirac true)) = 1 := by
  rw [totalVariation_iterate_bool_dirac_eq_rowSeparation_pow]
  norm_num [identity, totalVariation_bool, dirac_apply]

/-- Exporting a channel row to Mathlib PMF and back loses no probability information. -/
theorem binaryNoise_pmf_roundtrip (bit : Bool) :
    ProbabilityVector.ofPMF (binaryNoise bit).toPMF = binaryNoise bit :=
  ofPMF_toPMF _

end FiniteMarkovKernels.Examples
