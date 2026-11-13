/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteMarkovKernels.MarkovKernelContraction

/-!
# Block ergodicity for finite Markov kernels

This file derives stationary-law uniqueness and quantitative attraction from a strict
total-variation contraction coefficient at a finite temporal block.

## Main Results

- `FiniteMarkovKernel.IsStationary`.
- `FiniteMarkovKernel.IsStationary.iterate`.
- `FiniteMarkovKernel.eq_of_isStationary_of_contractionCoefficient_lt_one`.
- `FiniteMarkovKernel.totalVariation_iterate_stationary_le`.
- `FiniteMarkovKernel.eq_of_isStationary_of_iterate_contractionCoefficient_lt_one`.
- `FiniteMarkovKernel.totalVariation_blockIterate_stationary_le`.
- `FiniteMarkovKernel.totalVariation_iterate_block_mul_stationary_le`.
- `FiniteMarkovKernel.totalVariation_iterate_block_mul_add_stationary_le`.
-/

@[expose] public section

namespace FiniteMarkovKernels

open scoped BigOperators

universe u

namespace FiniteMarkovKernel

open ProbabilityVector

variable {A : Type u} [Fintype A] [Nonempty A] [DecidableEq A]

/-- A probability vector is stationary when applying the kernel leaves it unchanged. -/
def IsStationary (kernel : FiniteMarkovKernel A A) (law : ProbabilityVector A) : Prop :=
  kernel.apply law = law

namespace IsStationary

omit [Nonempty A] in
/-- A stationary law is fixed by every finite iterate of its kernel. -/
theorem iterate {kernel : FiniteMarkovKernel A A} {law : ProbabilityVector A}
    (hstationary : IsStationary kernel law) (n : ℕ) :
    IsStationary (FiniteMarkovKernel.iterate kernel n) law := by
  induction n with
  | zero =>
      exact FiniteMarkovKernel.iterate_zero_apply kernel law
  | succ n ih =>
      change (FiniteMarkovKernel.iterate kernel (n + 1)).apply law = law
      rw [FiniteMarkovKernel.iterate_succ_apply, ih, hstationary]

end IsStationary

omit [DecidableEq A] in
/-- A strictly contractive finite kernel has at most one stationary probability vector. -/
theorem eq_of_isStationary_of_contractionCoefficient_lt_one
    (kernel : FiniteMarkovKernel A A) {p q : ProbabilityVector A}
    (hp : IsStationary kernel p) (hq : IsStationary kernel q)
    (hstrict : contractionCoefficient kernel < 1) :
    p = q := by
  have hcontraction :=
    totalVariation_apply_le_contractionCoefficient kernel p q
  rw [hp, hq] at hcontraction
  have hnonneg := totalVariation_nonneg p q
  have hcoefficient_nonneg := contractionCoefficient_nonneg kernel
  have hzero : totalVariation p q = 0 := by
    nlinarith
  exact (totalVariation_eq_zero_iff p q).mp hzero

/-- Iteration converges toward a stationary law at the kernel's contraction-coefficient rate. -/
theorem totalVariation_iterate_stationary_le
    (kernel : FiniteMarkovKernel A A) (n : ℕ) (p stationary : ProbabilityVector A)
    (hstationary : IsStationary kernel stationary) :
    totalVariation ((FiniteMarkovKernel.iterate kernel n).apply p) stationary ≤
      contractionCoefficient kernel ^ n * totalVariation p stationary := by
  calc
    totalVariation ((FiniteMarkovKernel.iterate kernel n).apply p) stationary =
        totalVariation ((FiniteMarkovKernel.iterate kernel n).apply p)
          ((FiniteMarkovKernel.iterate kernel n).apply stationary) := by
      rw [hstationary.iterate n]
    _ ≤ contractionCoefficient kernel ^ n * totalVariation p stationary :=
      totalVariation_iterate_le kernel n p stationary

/-- A strict contraction at any finite iterate makes the original kernel's stationary law unique. -/
theorem eq_of_isStationary_of_iterate_contractionCoefficient_lt_one
    (kernel : FiniteMarkovKernel A A) (block : ℕ) {p q : ProbabilityVector A}
    (hp : IsStationary kernel p) (hq : IsStationary kernel q)
    (hstrict : contractionCoefficient (FiniteMarkovKernel.iterate kernel block) < 1) :
    p = q :=
  eq_of_isStationary_of_contractionCoefficient_lt_one
    (FiniteMarkovKernel.iterate kernel block) (hp.iterate block) (hq.iterate block) hstrict

/-- Repeated temporal blocks attract every initial law toward a stationary law. -/
theorem totalVariation_blockIterate_stationary_le
    (kernel : FiniteMarkovKernel A A) (block n : ℕ)
    (p stationary : ProbabilityVector A) (hstationary : IsStationary kernel stationary) :
    totalVariation
        ((FiniteMarkovKernel.iterate (FiniteMarkovKernel.iterate kernel block) n).apply p)
        stationary ≤
      contractionCoefficient (FiniteMarkovKernel.iterate kernel block) ^ n *
        totalVariation p stationary :=
  totalVariation_iterate_stationary_le
    (FiniteMarkovKernel.iterate kernel block) n p stationary (hstationary.iterate block)

/-- A temporal depth divisible by the block size obeys the block contraction rate. -/
theorem totalVariation_iterate_block_mul_stationary_le
    (kernel : FiniteMarkovKernel A A) (block n : ℕ)
    (p stationary : ProbabilityVector A) (hstationary : IsStationary kernel stationary) :
    totalVariation ((FiniteMarkovKernel.iterate kernel (block * n)).apply p) stationary ≤
      contractionCoefficient (FiniteMarkovKernel.iterate kernel block) ^ n *
        totalVariation p stationary := by
  rw [← FiniteMarkovKernel.iterate_iterate]
  exact totalVariation_blockIterate_stationary_le
    kernel block n p stationary hstationary

/-- Extra temporal steps after complete blocks cannot worsen the block attraction bound. -/
theorem totalVariation_iterate_block_mul_add_stationary_le
    (kernel : FiniteMarkovKernel A A) (block n remainder : ℕ)
    (p stationary : ProbabilityVector A) (hstationary : IsStationary kernel stationary) :
    totalVariation
        ((FiniteMarkovKernel.iterate kernel (block * n + remainder)).apply p) stationary ≤
      contractionCoefficient (FiniteMarkovKernel.iterate kernel block) ^ n *
        totalVariation p stationary := by
  rw [FiniteMarkovKernel.iterate_add, FiniteMarkovKernel.apply_followedBy]
  calc
    totalVariation
        ((FiniteMarkovKernel.iterate kernel remainder).apply
          ((FiniteMarkovKernel.iterate kernel (block * n)).apply p))
        stationary =
        totalVariation
          ((FiniteMarkovKernel.iterate kernel remainder).apply
            ((FiniteMarkovKernel.iterate kernel (block * n)).apply p))
          ((FiniteMarkovKernel.iterate kernel remainder).apply stationary) := by
      rw [hstationary.iterate remainder]
    _ ≤ totalVariation
          ((FiniteMarkovKernel.iterate kernel (block * n)).apply p) stationary :=
      totalVariation_apply_le (FiniteMarkovKernel.iterate kernel remainder) _ _
    _ ≤ contractionCoefficient (FiniteMarkovKernel.iterate kernel block) ^ n *
          totalVariation p stationary :=
      totalVariation_iterate_block_mul_stationary_le
        kernel block n p stationary hstationary

end FiniteMarkovKernel

end FiniteMarkovKernels
