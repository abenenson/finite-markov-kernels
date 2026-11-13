/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteMarkovKernels.PMFAdapter
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Measure-theoretic total variation of finite laws

Mathlib's signed-measure total variation is the full variation measure. Its total mass is
**twice** the probability-distance convention `ProbabilityVector.totalVariation`.
-/

@[expose] public section

namespace FiniteMarkovKernels.ProbabilityVector

open MeasureTheory
open scoped BigOperators

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The total mass of Mathlib's variation measure is twice the finite TV distance. -/
theorem signedMeasure_totalVariation_univ (p q : ProbabilityVector A) :
    ((p.toPMF.toMeasure.toSignedMeasure - q.toPMF.toMeasure.toSignedMeasure).totalVariation
      Set.univ).toReal = 2 * totalVariation p q := by
  classical
  rw [SignedMeasure.totalVariation_eq_variation]
  have hmass :
      (p.toPMF.toMeasure.toSignedMeasure - q.toPMF.toMeasure.toSignedMeasure).variation
          Set.univ = ∑ a, ENNReal.ofReal |p a - q a| := by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [VectorMeasure.variation_apply_singleton]
    simp only [_root_.sub_apply, Measure.toSignedMeasure_apply_measurable
      (measurableSet_singleton a), Measure.real,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
      toPMF_apply, ENNReal.toReal_ofReal (p.nonneg a),
      ENNReal.toReal_ofReal (q.nonneg a), Real.enorm_eq_ofReal_abs]
  rw [hmass, ← ENNReal.ofReal_sum_of_nonneg (fun a _ha ↦ abs_nonneg (p a - q a)),
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun a _ha ↦ abs_nonneg (p a - q a))]
  unfold totalVariation
  ring

/-- Finite TV is half the total mass of Mathlib's signed-measure variation. -/
theorem totalVariation_eq_half_signedMeasure (p q : ProbabilityVector A) :
    totalVariation p q = (1 / 2 : ℝ) *
      ((p.toPMF.toMeasure.toSignedMeasure - q.toPMF.toMeasure.toSignedMeasure).totalVariation
        Set.univ).toReal := by
  rw [signedMeasure_totalVariation_univ]
  ring

end FiniteMarkovKernels.ProbabilityVector
