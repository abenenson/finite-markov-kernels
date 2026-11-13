/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteMarkovKernels.MarkovKernelContraction

/-!
# Dobrushin row coefficient for finite Markov kernels

This file defines the maximum pairwise total-variation separation of a finite kernel's rows and
relates it to mixtures of those rows.

## Main Results

- `FiniteMarkovKernel.rowContractionCoefficient`.
- `FiniteMarkovKernel.rowTotalVariation_le_rowContractionCoefficient`.
- `FiniteMarkovKernel.totalVariation_apply_le_rowContractionCoefficient`.
- `FiniteMarkovKernel.rowContractionCoefficient_le_contractionCoefficient`.
-/

@[expose] public section

namespace FiniteMarkovKernels

open scoped BigOperators

universe u v

namespace ProbabilityVector

variable {A : Type u} [Fintype A]

/-- Total variation is one minus the common coordinate mass of two finite probability vectors. -/
theorem totalVariation_eq_one_sub_sum_min (p q : ProbabilityVector A) :
    totalVariation p q = 1 - ∑ a, min (p a) (q a) := by
  have hcoordinate (a : A) :
      |p a - q a| = p a + q a - 2 * min (p a) (q a) := by
    rcases le_total (p a) (q a) with hpq | hqp
    · rw [min_eq_left hpq, abs_of_nonpos (sub_nonpos.mpr hpq)]
      ring
    · rw [min_eq_right hqp, abs_of_nonneg (sub_nonneg.mpr hqp)]
      ring
  unfold totalVariation
  simp_rw [hcoordinate]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, p.sum_eq_one, q.sum_eq_one,
    ← Finset.mul_sum]
  ring

/-- Removing common coordinate mass from the left law leaves total-variation mass. -/
theorem sum_sub_min_eq_totalVariation_left (p q : ProbabilityVector A) :
    ∑ a, (p a - min (p a) (q a)) = totalVariation p q := by
  rw [Finset.sum_sub_distrib, p.sum_eq_one, totalVariation_eq_one_sub_sum_min]

/-- Removing common coordinate mass from the right law leaves total-variation mass. -/
theorem sum_sub_min_eq_totalVariation_right (p q : ProbabilityVector A) :
    ∑ a, (q a - min (p a) (q a)) = totalVariation p q := by
  rw [Finset.sum_sub_distrib, q.sum_eq_one, totalVariation_eq_one_sub_sum_min]

/-- The normalized part of `p` left after removing its coordinatewise common mass with `q`. -/
noncomputable def normalizedDifference (p q : ProbabilityVector A)
    (hpositive : 0 < totalVariation p q) : ProbabilityVector A where
  prob a := (p a - min (p a) (q a)) / totalVariation p q
  nonneg a := div_nonneg (sub_nonneg.mpr (min_le_left _ _)) hpositive.le
  sum_eq_one := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, sum_sub_min_eq_totalVariation_left]
    exact mul_inv_cancel₀ hpositive.ne'

/-- Coordinates of the normalized residual after removing common mass. -/
@[simp]
theorem normalizedDifference_apply (p q : ProbabilityVector A)
    (hpositive : 0 < totalVariation p q) (a : A) :
    normalizedDifference p q hpositive a =
      (p a - min (p a) (q a)) / totalVariation p q :=
  rfl

end ProbabilityVector

namespace FiniteMarkovKernel

open ProbabilityVector

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B] [Nonempty A]

/-- Maximum pairwise total-variation separation between the rows of a finite kernel. -/
noncomputable def rowContractionCoefficient (kernel : FiniteMarkovKernel A B) : ℝ :=
  sSup (Set.range fun pair : A × A ↦ totalVariation (kernel pair.1) (kernel pair.2))

omit [Fintype A] [Nonempty A] in
private theorem rowTotalVariation_range_bddAbove (kernel : FiniteMarkovKernel A B) :
    BddAbove (Set.range fun pair : A × A ↦
      totalVariation (kernel pair.1) (kernel pair.2)) :=
  ⟨1, Set.forall_mem_range.2 fun pair ↦ totalVariation_le_one (kernel pair.1) (kernel pair.2)⟩

omit [Fintype A] [Nonempty A] in
/-- Every pairwise row separation is bounded by the row contraction coefficient. -/
theorem rowTotalVariation_le_rowContractionCoefficient
    (kernel : FiniteMarkovKernel A B) (a a' : A) :
    totalVariation (kernel a) (kernel a') ≤ rowContractionCoefficient kernel := by
  apply le_csSup (rowTotalVariation_range_bddAbove kernel)
  exact ⟨(a, a'), rfl⟩

omit [Fintype A] in
/-- The row contraction coefficient is nonnegative. -/
theorem rowContractionCoefficient_nonneg (kernel : FiniteMarkovKernel A B) :
    0 ≤ rowContractionCoefficient kernel := by
  let a : A := Classical.arbitrary A
  simpa only [totalVariation_self] using
    rowTotalVariation_le_rowContractionCoefficient kernel a a

omit [Fintype A] in
/-- The row contraction coefficient is at most one. -/
theorem rowContractionCoefficient_le_one (kernel : FiniteMarkovKernel A B) :
    rowContractionCoefficient kernel ≤ 1 := by
  let a : A := Classical.arbitrary A
  apply csSup_le
  · exact ⟨0, ⟨(a, a), totalVariation_self (kernel a)⟩⟩
  · rintro _ ⟨pair, rfl⟩
    exact totalVariation_le_one (kernel pair.1) (kernel pair.2)

omit [Nonempty A] in
/-- The distance between any two mixtures of a kernel's rows is at most its row coefficient. -/
theorem totalVariation_apply_le_rowContractionCoefficient
    (kernel : FiniteMarkovKernel A B) (p q : ProbabilityVector A) :
    totalVariation (kernel.apply p) (kernel.apply q) ≤
      rowContractionCoefficient kernel := by
  have hrewrite (b : B) :
      (∑ a, p a * kernel a b) - ∑ a', q a' * kernel a' b =
        ∑ a, ∑ a', p a * q a' * (kernel a b - kernel a' b) := by
    calc
      (∑ a, p a * kernel a b) - ∑ a', q a' * kernel a' b =
          (∑ a, p a * kernel a b) * (∑ a', q a') -
            (∑ a, p a) * ∑ a', q a' * kernel a' b := by
        rw [p.sum_eq_one, q.sum_eq_one, mul_one, one_mul]
      _ = ∑ a, ∑ a', p a * q a' * (kernel a b - kernel a' b) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _ha
        apply Finset.sum_congr rfl
        intro a' _ha'
        ring
  have habs (b : B) :
      |∑ a, ∑ a', p a * q a' * (kernel a b - kernel a' b)| ≤
        ∑ a, ∑ a', p a * q a' * |kernel a b - kernel a' b| := by
    calc
      |∑ a, ∑ a', p a * q a' * (kernel a b - kernel a' b)| ≤
          ∑ a, |∑ a', p a * q a' * (kernel a b - kernel a' b)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ a', |p a * q a' * (kernel a b - kernel a' b)| := by
        gcongr with a
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, ∑ a', p a * q a' * |kernel a b - kernel a' b| := by
        apply Finset.sum_congr rfl
        intro a _ha
        apply Finset.sum_congr rfl
        intro a' _ha'
        rw [abs_mul, abs_mul, abs_of_nonneg (p.nonneg a), abs_of_nonneg (q.nonneg a')]
  have hcommute :
      (∑ b, ∑ a, ∑ a', p a * q a' * |kernel a b - kernel a' b|) =
        ∑ a, ∑ a', ∑ b, p a * q a' * |kernel a b - kernel a' b| := by
    calc
      (∑ b, ∑ a, ∑ a', p a * q a' * |kernel a b - kernel a' b|) =
          ∑ a, ∑ b, ∑ a', p a * q a' * |kernel a b - kernel a' b| :=
        Finset.sum_comm
      _ = ∑ a, ∑ a', ∑ b, p a * q a' * |kernel a b - kernel a' b| := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact Finset.sum_comm
  unfold totalVariation
  simp only [apply_prob, hrewrite]
  calc
    (1 / 2 : ℝ) * ∑ b, |∑ a, ∑ a', p a * q a' * (kernel a b - kernel a' b)| ≤
        (1 / 2 : ℝ) *
          ∑ b, ∑ a, ∑ a', p a * q a' * |kernel a b - kernel a' b| := by
      gcongr with b
      exact habs b
    _ = ∑ a, ∑ a', p a * q a' *
          ((1 / 2 : ℝ) * ∑ b, |kernel a b - kernel a' b|) := by
      rw [hcommute]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a' _ha'
      rw [← Finset.mul_sum]
      ring
    _ ≤ ∑ a, ∑ a', p a * q a' * rowContractionCoefficient kernel := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro a' _ha'
      apply mul_le_mul_of_nonneg_left
      · exact rowTotalVariation_le_rowContractionCoefficient kernel a a'
      · exact mul_nonneg (p.nonneg a) (q.nonneg a')
    _ = rowContractionCoefficient kernel := by
      have hinner (a : A) :
          (∑ a', q a' * rowContractionCoefficient kernel) =
            rowContractionCoefficient kernel := by
        rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
      calc
        (∑ a, ∑ a', p a * q a' * rowContractionCoefficient kernel) =
            ∑ a, p a * (∑ a', q a' * rowContractionCoefficient kernel) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a' _ha'
          ring
        _ = ∑ a, p a * rowContractionCoefficient kernel := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [hinner a]
        _ = rowContractionCoefficient kernel := by
          rw [← Finset.sum_mul, p.sum_eq_one, one_mul]

omit [Nonempty A] in
/-- Kernel application scales through the normalized residual laws of two distinct inputs. -/
theorem totalVariation_apply_eq_mul_residual
    (kernel : FiniteMarkovKernel A B) (p q : ProbabilityVector A)
    (hpositive : 0 < totalVariation p q) :
    totalVariation (kernel.apply p) (kernel.apply q) =
      totalVariation p q *
        totalVariation
          (kernel.apply (ProbabilityVector.normalizedDifference p q hpositive))
          (kernel.apply (ProbabilityVector.normalizedDifference q p
            (by simpa only [totalVariation_comm] using hpositive))) := by
  let residualP := ProbabilityVector.normalizedDifference p q hpositive
  let residualQ := ProbabilityVector.normalizedDifference q p <|
    by simpa only [totalVariation_comm] using hpositive
  have hresidual (a : A) :
      residualP a - residualQ a = (p a - q a) / totalVariation p q := by
    simp only [residualP, residualQ, ProbabilityVector.normalizedDifference_apply]
    rw [min_comm (q a) (p a)]
    rw [totalVariation_comm q p]
    field_simp
    ring
  have hcoordinate (b : B) :
      kernel.apply p b - kernel.apply q b =
        totalVariation p q * (kernel.apply residualP b - kernel.apply residualQ b) := by
    simp only [apply_prob, ← Finset.sum_sub_distrib]
    calc
      (∑ a, (p a * kernel a b - q a * kernel a b)) =
          ∑ a, (p a - q a) * kernel a b := by
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ = ∑ a, totalVariation p q * (residualP a - residualQ a) * kernel a b := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [hresidual]
        field_simp
      _ = totalVariation p q *
          (∑ a, (residualP a * kernel a b - residualQ a * kernel a b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
  change
    (1 / 2 : ℝ) * ∑ b, |kernel.apply p b - kernel.apply q b| =
      totalVariation p q *
        ((1 / 2 : ℝ) * ∑ b, |kernel.apply residualP b - kernel.apply residualQ b|)
  simp_rw [hcoordinate, abs_mul, abs_of_nonneg hpositive.le]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  ring

/-- The global contraction coefficient is no greater than the Dobrushin row coefficient. -/
theorem contractionCoefficient_le_rowContractionCoefficient
    (kernel : FiniteMarkovKernel A B) :
    contractionCoefficient kernel ≤ rowContractionCoefficient kernel := by
  apply contractionCoefficient_le_of_ratio_le
  intro p q
  unfold contractionRatio
  split_ifs with hzero
  · exact rowContractionCoefficient_nonneg kernel
  · have hpositive : 0 < totalVariation p q :=
      lt_of_le_of_ne (totalVariation_nonneg p q) (Ne.symm hzero)
    rw [totalVariation_apply_eq_mul_residual kernel p q hpositive]
    field_simp
    exact totalVariation_apply_le_rowContractionCoefficient kernel _ _

/-- The row coefficient is no greater than the global contraction coefficient. -/
theorem rowContractionCoefficient_le_contractionCoefficient [DecidableEq A]
    (kernel : FiniteMarkovKernel A B) :
    rowContractionCoefficient kernel ≤ contractionCoefficient kernel := by
  let a : A := Classical.arbitrary A
  apply csSup_le
  · exact ⟨0, ⟨(a, a), totalVariation_self (kernel a)⟩⟩
  · rintro _ ⟨pair, rfl⟩
    rcases pair with ⟨x, y⟩
    by_cases hxy : x = y
    · simp [hxy, contractionCoefficient_nonneg kernel]
    · have hratio :
          contractionRatio kernel (ProbabilityVector.dirac x) (ProbabilityVector.dirac y) =
            totalVariation (kernel x) (kernel y) := by
        simp [contractionRatio, hxy]
      change totalVariation (kernel x) (kernel y) ≤ contractionCoefficient kernel
      rw [← hratio]
      exact contractionRatio_le_contractionCoefficient kernel _ _

/-- Dobrushin's formula: global total-variation contraction is maximum row separation. -/
theorem contractionCoefficient_eq_rowContractionCoefficient [DecidableEq A]
    (kernel : FiniteMarkovKernel A B) :
    contractionCoefficient kernel = rowContractionCoefficient kernel :=
  le_antisymm
    (contractionCoefficient_le_rowContractionCoefficient kernel)
    (rowContractionCoefficient_le_contractionCoefficient kernel)

end FiniteMarkovKernel

end FiniteMarkovKernels
