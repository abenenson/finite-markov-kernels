/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteMarkovKernels.BlockErgodicity

/-!
# Perturbation bounds for finite Markov kernels

This file bounds the effect of a rowwise kernel perturbation on finite-time laws and stationary
laws. The stationary bound uses a strict contraction at a supplied finite temporal block.

## Main Results

- `FiniteMarkovKernel.rowDiscrepancy`.
- `FiniteMarkovKernel.totalVariation_apply_same_le_rowDiscrepancy`.
- `FiniteMarkovKernel.totalVariation_iterate_same_le`.
- `FiniteMarkovKernel.totalVariation_isStationary_le`.
-/

@[expose] public section

namespace FiniteMarkovKernels

open scoped BigOperators

universe u

namespace FiniteMarkovKernel

open ProbabilityVector

variable {A : Type u} [Fintype A] [Nonempty A] [DecidableEq A]

/-- Maximum total-variation distance between corresponding rows of two finite kernels. -/
noncomputable def rowDiscrepancy
    (kernel perturbed : FiniteMarkovKernel A A) : ℝ :=
  sSup (Set.range fun state : A ↦ totalVariation (kernel state) (perturbed state))

omit [Nonempty A] [DecidableEq A] in
private theorem rowDiscrepancy_range_bddAbove
    (kernel perturbed : FiniteMarkovKernel A A) :
    BddAbove (Set.range fun state : A ↦
      totalVariation (kernel state) (perturbed state)) :=
  ⟨1, Set.forall_mem_range.2 fun state ↦
    totalVariation_le_one (kernel state) (perturbed state)⟩

omit [Nonempty A] [DecidableEq A] in
/-- Every corresponding row distance is bounded by the row discrepancy. -/
theorem rowTotalVariation_le_rowDiscrepancy
    (kernel perturbed : FiniteMarkovKernel A A) (state : A) :
    totalVariation (kernel state) (perturbed state) ≤
      rowDiscrepancy kernel perturbed := by
  apply le_csSup (rowDiscrepancy_range_bddAbove kernel perturbed)
  exact ⟨state, rfl⟩

omit [DecidableEq A] in
/-- Row discrepancy is nonnegative. -/
theorem rowDiscrepancy_nonneg
    (kernel perturbed : FiniteMarkovKernel A A) :
    0 ≤ rowDiscrepancy kernel perturbed := by
  let state : A := Classical.arbitrary A
  exact (totalVariation_nonneg (kernel state) (perturbed state)).trans
    (rowTotalVariation_le_rowDiscrepancy kernel perturbed state)

omit [Nonempty A] [DecidableEq A] in
/-- Applying two kernels to the same law differs by at most their row discrepancy. -/
theorem totalVariation_apply_same_le_rowDiscrepancy
    (kernel perturbed : FiniteMarkovKernel A A) (law : ProbabilityVector A) :
    totalVariation (kernel.apply law) (perturbed.apply law) ≤
      rowDiscrepancy kernel perturbed := by
  have hrewrite (output : A) :
      (∑ state, law state * kernel state output) -
          ∑ state, law state * perturbed state output =
        ∑ state, law state * (kernel state output - perturbed state output) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro state _hstate
    ring
  unfold totalVariation
  simp only [apply_prob, hrewrite]
  calc
    (1 / 2 : ℝ) *
        ∑ output, |∑ state, law state *
          (kernel state output - perturbed state output)| ≤
      (1 / 2 : ℝ) *
        ∑ output, ∑ state, law state *
          |kernel state output - perturbed state output| := by
      gcongr with output
      calc
        |∑ state, law state * (kernel state output - perturbed state output)| ≤
            ∑ state, |law state *
              (kernel state output - perturbed state output)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ state, law state *
              |kernel state output - perturbed state output| := by
          apply Finset.sum_congr rfl
          intro state _hstate
          rw [abs_mul, abs_of_nonneg (law.nonneg state)]
    _ = ∑ state, law state *
          ((1 / 2 : ℝ) *
            ∑ output, |kernel state output - perturbed state output|) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro state _hstate
      rw [← Finset.mul_sum]
      ring
    _ ≤ ∑ state, law state * rowDiscrepancy kernel perturbed := by
      apply Finset.sum_le_sum
      intro state _hstate
      exact mul_le_mul_of_nonneg_left
        (rowTotalVariation_le_rowDiscrepancy kernel perturbed state)
        (law.nonneg state)
    _ = rowDiscrepancy kernel perturbed := by
      rw [← Finset.sum_mul, law.sum_eq_one, one_mul]

omit [Nonempty A] in
/-- After `n` steps, a common initial law differs by at most `n` row discrepancies. -/
theorem totalVariation_iterate_same_le
    (kernel perturbed : FiniteMarkovKernel A A) (n : ℕ)
    (law : ProbabilityVector A) :
    totalVariation
        ((iterate kernel n).apply law) ((iterate perturbed n).apply law) ≤
      n * rowDiscrepancy kernel perturbed := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [iterate_succ_apply, iterate_succ_apply]
      calc
        totalVariation
            (kernel.apply ((iterate kernel n).apply law))
            (perturbed.apply ((iterate perturbed n).apply law)) ≤
          totalVariation
              (kernel.apply ((iterate kernel n).apply law))
              (kernel.apply ((iterate perturbed n).apply law)) +
            totalVariation
              (kernel.apply ((iterate perturbed n).apply law))
              (perturbed.apply ((iterate perturbed n).apply law)) :=
          totalVariation_triangle _ _ _
        _ ≤ totalVariation
              ((iterate kernel n).apply law) ((iterate perturbed n).apply law) +
            rowDiscrepancy kernel perturbed :=
          add_le_add
            (totalVariation_apply_le kernel _ _)
            (totalVariation_apply_same_le_rowDiscrepancy kernel perturbed _)
        _ ≤ n * rowDiscrepancy kernel perturbed +
            rowDiscrepancy kernel perturbed :=
          add_le_add ih le_rfl
        _ = ((n : ℝ) + 1) * rowDiscrepancy kernel perturbed := by ring
        _ = ((n + 1 : ℕ) : ℝ) * rowDiscrepancy kernel perturbed := by
          rw [Nat.cast_add, Nat.cast_one]

/-- Stationary laws are stable under rowwise perturbation when one kernel has a strict block. -/
theorem totalVariation_isStationary_le
    (kernel perturbed : FiniteMarkovKernel A A) (block : ℕ)
    (stationary perturbedStationary : ProbabilityVector A)
    (hstationary : IsStationary kernel stationary)
    (hperturbedStationary : IsStationary perturbed perturbedStationary)
    (hstrict : contractionCoefficient (iterate kernel block) < 1) :
    totalVariation stationary perturbedStationary ≤
      block * rowDiscrepancy kernel perturbed /
        (1 - contractionCoefficient (iterate kernel block)) := by
  have hbound :
      totalVariation stationary perturbedStationary ≤
        contractionCoefficient (iterate kernel block) *
            totalVariation stationary perturbedStationary +
          block * rowDiscrepancy kernel perturbed := by
    calc
      totalVariation stationary perturbedStationary =
          totalVariation
            ((iterate kernel block).apply stationary)
            ((iterate perturbed block).apply perturbedStationary) := by
        rw [hstationary.iterate block, hperturbedStationary.iterate block]
      _ ≤ totalVariation
            ((iterate kernel block).apply stationary)
            ((iterate kernel block).apply perturbedStationary) +
          totalVariation
            ((iterate kernel block).apply perturbedStationary)
            ((iterate perturbed block).apply perturbedStationary) :=
        totalVariation_triangle _ _ _
      _ ≤ contractionCoefficient (iterate kernel block) *
            totalVariation stationary perturbedStationary +
          block * rowDiscrepancy kernel perturbed :=
        add_le_add
          (totalVariation_apply_le_contractionCoefficient
            (iterate kernel block) stationary perturbedStationary)
          (totalVariation_iterate_same_le kernel perturbed block perturbedStationary)
  have hdenominator : 0 < 1 - contractionCoefficient (iterate kernel block) :=
    sub_pos.mpr hstrict
  apply (le_div_iff₀ hdenominator).2
  nlinarith

end FiniteMarkovKernel

end FiniteMarkovKernels
