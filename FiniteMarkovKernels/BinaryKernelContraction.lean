/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import FiniteMarkovKernels.DobrushinCoefficient

/-!
# Exact total-variation contraction of binary kernels

The signed difference of two probability laws on `Bool` is one-dimensional. Consequently, every
finite Markov kernel with binary input scales total variation exactly by the separation of its two
rows. For a binary endomorphism this identity iterates, giving an exact geometric law rather than
only the usual Dobrushin upper bound.

## Main Results

- `ProbabilityVector.totalVariation_bool`: binary total variation is one coordinate difference.
- `FiniteMarkovKernel.totalVariation_apply_bool_eq_rowSeparation_mul`: exact one-step scaling.
- `FiniteMarkovKernel.totalVariation_iterate_bool_eq_rowSeparation_pow_mul`: exact finite-lag
  scaling.
- `FiniteMarkovKernel.totalVariation_iterate_bool_dirac_pos`: distinct point inputs remain
  distinct at every finite lag when the row separation is positive.
- `FiniteMarkovKernel.tendsto_totalVariation_iterate_bool_dirac_zero`: strict row contraction
  erases the initial distinction asymptotically.
-/

@[expose] public section

namespace FiniteMarkovKernels

open Filter
open scoped BigOperators

universe u

namespace ProbabilityVector

/-- Total variation between Boolean laws is the absolute difference of either coordinate. -/
theorem totalVariation_bool (p q : ProbabilityVector Bool) :
    totalVariation p q = |p false - q false| := by
  have hp := p.sum_eq_one
  have hq := q.sum_eq_one
  rw [Fintype.sum_bool] at hp hq
  have htrue : p true - q true = -(p false - q false) := by
    linarith
  unfold totalVariation
  rw [Fintype.sum_bool, htrue, abs_neg]
  ring

end ProbabilityVector

namespace FiniteMarkovKernel

variable {B : Type u} [Fintype B]

/-- Every binary-input kernel scales total variation exactly by its row separation. -/
theorem totalVariation_apply_bool_eq_rowSeparation_mul
    (kernel : FiniteMarkovKernel Bool B)
    (p q : ProbabilityVector Bool) :
    ProbabilityVector.totalVariation (kernel.apply p) (kernel.apply q) =
      ProbabilityVector.totalVariation (kernel false) (kernel true) *
        ProbabilityVector.totalVariation p q := by
  have hp := p.sum_eq_one
  have hq := q.sum_eq_one
  rw [Fintype.sum_bool] at hp hq
  have hpTrue : p true = 1 - p false := by
    linarith
  have hqTrue : q true = 1 - q false := by
    linarith
  have hcoordinate (b : B) :
      kernel.apply p b - kernel.apply q b =
        (p false - q false) * (kernel false b - kernel true b) := by
    simp only [apply_prob, Fintype.sum_bool]
    rw [hpTrue, hqTrue]
    ring
  rw [ProbabilityVector.totalVariation_bool p q]
  unfold ProbabilityVector.totalVariation
  simp_rw [hcoordinate, abs_mul]
  rw [← Finset.mul_sum]
  ring

/-- A binary endomorphism has exact geometric total-variation scaling at every finite lag. -/
theorem totalVariation_iterate_bool_eq_rowSeparation_pow_mul
    (kernel : FiniteMarkovKernel Bool Bool) (steps : ℕ)
    (p q : ProbabilityVector Bool) :
    ProbabilityVector.totalVariation
        ((iterate kernel steps).apply p)
        ((iterate kernel steps).apply q) =
      ProbabilityVector.totalVariation (kernel false) (kernel true) ^ steps *
        ProbabilityVector.totalVariation p q := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      rw [iterate_succ_apply, iterate_succ_apply,
        totalVariation_apply_bool_eq_rowSeparation_mul, ih, pow_succ]
      ring

/-- Opposite Boolean point inputs have exact finite-lag separation equal to the row separation
raised to the lag. -/
theorem totalVariation_iterate_bool_dirac_eq_rowSeparation_pow
    (kernel : FiniteMarkovKernel Bool Bool) (steps : ℕ) :
    ProbabilityVector.totalVariation
        ((iterate kernel steps).apply (ProbabilityVector.dirac false))
        ((iterate kernel steps).apply (ProbabilityVector.dirac true)) =
      ProbabilityVector.totalVariation (kernel false) (kernel true) ^ steps := by
  rw [totalVariation_iterate_bool_eq_rowSeparation_pow_mul]
  simp

/-- Positive row separation preserves a positive distinction between opposite point inputs at
every finite lag. -/
theorem totalVariation_iterate_bool_dirac_pos
    (kernel : FiniteMarkovKernel Bool Bool)
    (hRows : 0 < ProbabilityVector.totalVariation (kernel false) (kernel true))
    (steps : ℕ) :
    0 <
      ProbabilityVector.totalVariation
        ((iterate kernel steps).apply (ProbabilityVector.dirac false))
        ((iterate kernel steps).apply (ProbabilityVector.dirac true)) := by
  rw [totalVariation_iterate_bool_dirac_eq_rowSeparation_pow]
  exact pow_pos hRows steps

/-- Strict row contraction erases the distinction between opposite Boolean point inputs
asymptotically. -/
theorem tendsto_totalVariation_iterate_bool_dirac_zero
    (kernel : FiniteMarkovKernel Bool Bool)
    (hRows : ProbabilityVector.totalVariation (kernel false) (kernel true) < 1) :
    Tendsto
      (fun steps ↦
        ProbabilityVector.totalVariation
          ((iterate kernel steps).apply (ProbabilityVector.dirac false))
          ((iterate kernel steps).apply (ProbabilityVector.dirac true)))
      atTop (nhds 0) := by
  simpa only [totalVariation_iterate_bool_dirac_eq_rowSeparation_pow] using
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (ProbabilityVector.totalVariation_nonneg (kernel false) (kernel true)) hRows

end FiniteMarkovKernel

end FiniteMarkovKernels
