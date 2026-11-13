/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteMarkovKernels.ProbabilityVectorDisintegration

/-!
# Disintegration with a zero-mass marginal

A joint law concentrated at `(false, true)` has a genuinely unconstrained conditional on the
outer value `true`. Changing that conditional from `dirac false` to `dirac true` changes the
conditional row while leaving the reconstructed joint law unchanged.
-/

@[expose] public section

namespace FiniteMarkovKernels.Examples

open ProbabilityVector

/-- A joint law with one occupied fiber and one zero-mass fiber. -/
noncomputable def degenerateJoint : ProbabilityVector (Σ _ : Bool, Bool) :=
  dirac ⟨false, true⟩

/-- The outer value `true` has zero probability in the example joint law. -/
theorem degenerateJoint_zero_marginal : firstMarginal degenerateJoint true = 0 := by
  norm_num [firstMarginal, degenerateJoint, dirac_apply, Fintype.sum_bool]

/-- The occupied fiber has conditional law `dirac true`, independently of the fallback. -/
theorem degenerateJoint_occupied_conditional (fallback : ∀ _ : Bool, ProbabilityVector Bool) :
    conditionalRows degenerateJoint fallback false = dirac true := by
  apply ProbabilityVector.ext
  intro bit
  cases bit <;>
    norm_num [conditionalRows, firstMarginal, degenerateJoint, dirac_apply, Fintype.sum_bool]
  decide

/-- Different fallbacks really do give different conditionals on the zero-mass fiber. -/
theorem degenerateJoint_null_conditionals_differ :
    conditionalRows degenerateJoint (fun _ ↦ dirac false) true ≠
      conditionalRows degenerateJoint (fun _ ↦ dirac true) true := by
  rw [conditionalRows_of_firstMarginal_eq_zero _ _ _ degenerateJoint_zero_marginal,
    conditionalRows_of_firstMarginal_eq_zero _ _ _ degenerateJoint_zero_marginal]
  intro h
  have hmass := congrArg (fun law : ProbabilityVector Bool ↦ law false) h
  norm_num [dirac_apply] at hmass

/-- Both distinct null-fiber choices reconstruct the same complete joint law. -/
theorem degenerateJoint_reconstruction :
    compound (firstMarginal degenerateJoint)
        (conditionalRows degenerateJoint (fun _ ↦ dirac false)) = degenerateJoint ∧
      compound (firstMarginal degenerateJoint)
        (conditionalRows degenerateJoint (fun _ ↦ dirac true)) = degenerateJoint := by
  exact ⟨compound_firstMarginal_conditionalRows _ _, compound_firstMarginal_conditionalRows _ _⟩

end FiniteMarkovKernels.Examples
