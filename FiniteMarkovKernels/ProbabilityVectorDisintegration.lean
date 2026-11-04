/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Algebra.BigOperators.Field
import FiniteMarkovKernels.ProbabilityVector

/-!
# Finite probability-vector disintegration

Given a fallback probability row on each fiber, this file factors a finite dependent joint
probability vector into its first marginal and conditional rows. The fallback supplies the
conditional on zero-mass marginal coordinates; the reconstructed joint law is independent
of that choice.

## Main Results

- `ProbabilityVector.firstMarginal`: the outer marginal of a dependent joint law.
- `ProbabilityVector.conditionalRows`: normalized conditional rows with zero-mass fallbacks.
- `ProbabilityVector.compound_firstMarginal_conditionalRows`: exact joint-law reconstruction.
-/

namespace FiniteMarkovKernels

open scoped BigOperators

universe u v

namespace ProbabilityVector

variable {A : Type u} {C : A → Type v} [Fintype A] [∀ a, Fintype (C a)]

/-- The first marginal of a finite dependent joint probability vector. -/
noncomputable def firstMarginal (joint : ProbabilityVector (Σ a, C a)) :
    ProbabilityVector A where
  prob a := ∑ c, joint ⟨a, c⟩
  nonneg a := Finset.sum_nonneg fun c _hc ↦ joint.nonneg ⟨a, c⟩
  sum_eq_one := by
    rw [← Fintype.sum_sigma]
    exact joint.sum_eq_one

/-- A zero first-marginal coordinate forces every corresponding joint coordinate to vanish. -/
theorem apply_eq_zero_of_firstMarginal_eq_zero
    (joint : ProbabilityVector (Σ a, C a)) {a : A}
    (ha : firstMarginal joint a = 0) (c : C a) :
    joint ⟨a, c⟩ = 0 := by
  have hall : (fun c : C a ↦ joint ⟨a, c⟩) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg fun c ↦ joint.nonneg ⟨a, c⟩).mp ha
  simpa using congrFun hall c

/-- Conditional rows of a finite dependent joint law.

On a zero-mass marginal coordinate, the explicitly supplied fallback row is used. -/
noncomputable def conditionalRows (joint : ProbabilityVector (Σ a, C a))
    (fallback : ∀ a, ProbabilityVector (C a)) :
    ∀ a, ProbabilityVector (C a) := fun a ↦
  if ha : firstMarginal joint a = 0 then fallback a else
    { prob := fun c ↦ joint ⟨a, c⟩ / firstMarginal joint a
      nonneg := fun c ↦
        div_nonneg (joint.nonneg ⟨a, c⟩) ((firstMarginal joint).nonneg a)
      sum_eq_one := by
        rw [← Finset.sum_div]
        change firstMarginal joint a / firstMarginal joint a = 1
        exact div_self ha }

/-- On a zero first-marginal coordinate, the conditional row is the chosen fallback. -/
@[simp]
theorem conditionalRows_of_firstMarginal_eq_zero
    (joint : ProbabilityVector (Σ a, C a))
    (fallback : ∀ a, ProbabilityVector (C a)) (a : A)
    (ha : firstMarginal joint a = 0) :
    conditionalRows joint fallback a = fallback a := by
  simp [conditionalRows, ha]

/-- On a nonzero first-marginal coordinate, the conditional is the normalized joint mass. -/
@[simp]
theorem conditionalRows_apply_of_firstMarginal_ne_zero
    (joint : ProbabilityVector (Σ a, C a))
    (fallback : ∀ a, ProbabilityVector (C a)) (a : A) (c : C a)
    (ha : firstMarginal joint a ≠ 0) :
    conditionalRows joint fallback a c =
      joint ⟨a, c⟩ / firstMarginal joint a := by
  simp [conditionalRows, ha]

/-- Compounding the first marginal with the conditional rows reconstructs the joint law exactly. -/
theorem compound_firstMarginal_conditionalRows
    (joint : ProbabilityVector (Σ a, C a))
    (fallback : ∀ a, ProbabilityVector (C a)) :
    compound (firstMarginal joint) (conditionalRows joint fallback) = joint := by
  apply ProbabilityVector.ext
  rintro ⟨a, c⟩
  by_cases ha : firstMarginal joint a = 0
  · rw [compound_apply, ha, zero_mul]
    exact (apply_eq_zero_of_firstMarginal_eq_zero joint ha c).symm
  · rw [compound_apply, conditionalRows_apply_of_firstMarginal_ne_zero _ _ _ _ ha]
    exact mul_div_cancel₀ _ ha

end ProbabilityVector

end FiniteMarkovKernels
