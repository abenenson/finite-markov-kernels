/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import FiniteMarkovKernels.MarkovKernelContraction

/-!
# Finite probability-mass-function adapter

This file transports finite `PMF` laws and kernels to the boundary-inclusive real probability
simplex used by the finite-kernel contraction calculus.

## Main Results

- `ProbabilityVector.ofPMF`.
- `ProbabilityVector.pmfEquiv`.
- `ProbabilityVector.ofPMF_injective`.
- `FiniteMarkovKernel.ofPMF`.
- `FiniteMarkovKernel.ofPMF_bind`.
- `FiniteMarkovKernel.ofPMF_followedBy`.
- `FiniteRowMarkovKernel.comp_toMeasure_eq_apply`.
- `FiniteRowMarkovKernel.rowsEquiv`.
- `SingletonMarkovKernel.probabilityVectorEquiv`.
-/

namespace FiniteMarkovKernels

open scoped BigOperators

universe u v

namespace ProbabilityVector

variable {A : Type u} [Fintype A]

/-- Transport a real finite probability vector to a probability mass function. -/
noncomputable def toPMF (law : ProbabilityVector A) : PMF A :=
  ⟨fun a ↦ ENNReal.ofReal (law a), by
    convert hasSum_fintype (fun a ↦ ENNReal.ofReal (law a)) using 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ha ↦ law.nonneg a), law.sum_eq_one]
    norm_num⟩

/-- Evaluation commutes with transport from real probability vectors to mass functions. -/
@[simp]
theorem toPMF_apply (law : ProbabilityVector A) (a : A) :
    toPMF law a = ENNReal.ofReal (law a) :=
  rfl

/-- The real probability vector associated to a finite probability mass function. -/
noncomputable def ofPMF (law : PMF A) : ProbabilityVector A where
  prob a := (law a).toReal
  nonneg _ := ENNReal.toReal_nonneg
  sum_eq_one := by
    have hsum : ∑ a : A, law a = 1 := by
      simpa only [tsum_fintype] using PMF.tsum_coe law
    rw [← ENNReal.toReal_sum (fun a _ha ↦ law.apply_ne_top a), hsum]
    norm_num

/-- A mass function's probability-vector coordinate is its real-valued mass. -/
@[simp]
theorem ofPMF_apply (law : PMF A) (a : A) :
    ofPMF law a = (law a).toReal :=
  rfl

/-- Transport from finite probability mass functions to probability vectors is injective. -/
theorem ofPMF_injective : Function.Injective (ofPMF : PMF A → ProbabilityVector A) := by
  intro p q hpq
  apply PMF.ext
  intro a
  have hcoordinate := congrArg (fun law : ProbabilityVector A ↦ law a) hpq
  exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp hcoordinate

/-- Two finite mass functions have the same probability vector exactly when they are equal. -/
@[simp]
theorem ofPMF_inj {p q : PMF A} :
    ofPMF p = ofPMF q ↔ p = q :=
  ofPMF_injective.eq_iff

/-- Transporting a probability vector to a mass function and back is the identity. -/
@[simp]
theorem ofPMF_toPMF (law : ProbabilityVector A) :
    ofPMF (toPMF law) = law := by
  apply ProbabilityVector.ext
  intro a
  change (ENNReal.ofReal (law a)).toReal = law a
  exact ENNReal.toReal_ofReal (law.nonneg a)

/-- Transporting a mass function to a probability vector and back is the identity. -/
@[simp]
theorem toPMF_ofPMF (law : PMF A) :
    toPMF (ofPMF law) = law := by
  apply PMF.ext
  intro a
  change ENNReal.ofReal (law a).toReal = law a
  exact ENNReal.ofReal_toReal (law.apply_ne_top a)

/-- Finite real probability vectors are equivalent to finite probability mass functions. -/
noncomputable def pmfEquiv : ProbabilityVector A ≃ PMF A where
  toFun := toPMF
  invFun := ofPMF
  left_inv := ofPMF_toPMF
  right_inv := toPMF_ofPMF

end ProbabilityVector

namespace FiniteMarkovKernel

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

/-- Transport a finite `PMF`-valued kernel to a real finite Markov kernel. -/
noncomputable def ofPMF (kernel : A → PMF B) : FiniteMarkovKernel A B :=
  fun a ↦ ProbabilityVector.ofPMF (kernel a)

omit [Fintype A] in
/-- Evaluating a transported PMF-valued kernel takes the real value of its mass. -/
@[simp]
theorem ofPMF_prob (kernel : A → PMF B) (a : A) (b : B) :
    ofPMF kernel a b = (kernel a b).toReal :=
  rfl

/-- `PMF.bind` agrees with finite-kernel application after transport to real probability vectors. -/
theorem ofPMF_bind (law : PMF A) (kernel : A → PMF B) :
    ProbabilityVector.ofPMF (law.bind kernel) =
      (ofPMF kernel).apply (ProbabilityVector.ofPMF law) := by
  apply ProbabilityVector.ext
  intro b
  simp only [ProbabilityVector.ofPMF_apply, PMF.bind_apply, apply_prob, ofPMF_prob]
  rw [tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _ha
    rw [ENNReal.toReal_mul]
  · intro a _ha
    exact ENNReal.mul_ne_top (law.apply_ne_top a) ((kernel a).apply_ne_top b)

omit [Fintype A] in
/-- Temporal composition after transport agrees with `PMF.bind` composition before transport. -/
theorem ofPMF_followedBy {C : Type*} [Fintype C]
    (kernel : A → PMF B) (later : B → PMF C) :
    (ofPMF kernel).followedBy (ofPMF later) =
      ofPMF fun a ↦ (kernel a).bind later := by
  funext a
  exact (ofPMF_bind (kernel a) later).symm

end FiniteMarkovKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Measure-theoretic Markov kernels between finite discrete spaces. -/
abbrev FiniteRowMarkovKernel
    (A B : Type*) [MeasurableSpace A] [MeasurableSpace B] :=
  {kernel : Kernel A B // IsMarkovKernel kernel}

namespace FiniteRowMarkovKernel

variable {A B : Type*} [Fintype A] [Fintype B]
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]

/-- Regard finite probability-vector rows as one measure-theoretic Markov kernel. -/
noncomputable def ofRows (rows : A → ProbabilityVector B) :
    FiniteRowMarkovKernel A B := by
  refine ⟨Kernel.ofFunOfCountable fun a ↦ (rows a).toPMF.toMeasure, ?_⟩
  exact ⟨fun a ↦ by
    change IsProbabilityMeasure ((rows a).toPMF.toMeasure)
    infer_instance⟩

/-- An encoded finite row assigns its original coordinate mass to each singleton. -/
@[simp]
theorem ofRows_apply_singleton (rows : A → ProbabilityVector B) (a : A) (b : B) :
    (ofRows rows).1 a {b} = ENNReal.ofReal (rows a b) := by
  change (rows a).toPMF.toMeasure {b} = ENNReal.ofReal (rows a b)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  rfl

/-- Recover every finite probability-vector row of a measure-theoretic Markov kernel. -/
noncomputable def toRows (kernel : FiniteRowMarkovKernel A B) :
    A → ProbabilityVector B :=
  fun a ↦ by
    letI : IsMarkovKernel kernel.1 := kernel.2
    letI : IsProbabilityMeasure (kernel.1 a) :=
      IsMarkovKernel.isProbabilityMeasure a
    exact ProbabilityVector.ofPMF ((kernel.1 a).toPMF)

/-- Recovering rows from their finite kernel returns the original row family. -/
@[simp]
theorem toRows_ofRows (rows : A → ProbabilityVector B) :
    toRows (ofRows rows) = rows := by
  funext a
  apply ProbabilityVector.ext
  intro b
  unfold toRows
  change (((rows a).toPMF.toMeasure).toPMF b).toReal = rows a b
  rw [PMF.toMeasure_toPMF]
  exact ENNReal.toReal_ofReal ((rows a).nonneg b)

/-- Re-encoding all rows of a finite Markov kernel returns the original kernel. -/
@[simp]
theorem ofRows_toRows (kernel : FiniteRowMarkovKernel A B) :
    ofRows (toRows kernel) = kernel := by
  apply Subtype.ext
  apply Kernel.ext
  intro a
  change (ProbabilityVector.toPMF (toRows kernel a)).toMeasure = kernel.1 a
  let : IsMarkovKernel kernel.1 := kernel.2
  let : IsProbabilityMeasure (kernel.1 a) :=
    IsMarkovKernel.isProbabilityMeasure a
  unfold toRows
  rw [ProbabilityVector.toPMF_ofPMF]
  exact Measure.toPMF_toMeasure (kernel.1 a)

/-- Finite row families are equivalent to finite measure-theoretic Markov kernels. -/
noncomputable def rowsEquiv :
    (A → ProbabilityVector B) ≃ FiniteRowMarkovKernel A B where
  toFun := ofRows
  invFun := toRows
  left_inv := toRows_ofRows
  right_inv := ofRows_toRows

/-- Composing encoded finite rows with an encoded finite law is finite kernel application. -/
theorem comp_toMeasure_eq_apply (law : ProbabilityVector A)
    (rows : A → ProbabilityVector B) :
    (ofRows rows).1 ∘ₘ law.toPMF.toMeasure =
      (FiniteMarkovKernel.apply rows law).toPMF.toMeasure := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.bind_apply (measurableSet_singleton b) (ofRows rows).1.aemeasurable]
  rw [lintegral_fintype]
  change
    (∑ a, (rows a).toPMF.toMeasure {b} * law.toPMF.toMeasure {a}) =
      (FiniteMarkovKernel.apply rows law).toPMF.toMeasure {b}
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ProbabilityVector.toPMF_apply, FiniteMarkovKernel.apply_prob]
  calc
    (∑ a, ENNReal.ofReal (rows a b) * ENNReal.ofReal (law a)) =
        ∑ a, ENNReal.ofReal (law a * rows a b) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [ENNReal.ofReal_mul (law.nonneg a)]
      exact mul_comm _ _
    _ = ENNReal.ofReal (∑ a, law a * rows a b) :=
      (ENNReal.ofReal_sum_of_nonneg fun a _ha ↦
        mul_nonneg (law.nonneg a) ((rows a).nonneg b)).symm

end FiniteRowMarkovKernel

/-- Measure-theoretic Markov kernels from a singleton input. -/
abbrev SingletonMarkovKernel (A : Type u) [MeasurableSpace A] :=
  {kernel : Kernel Unit A // IsMarkovKernel kernel}

namespace SingletonMarkovKernel

variable {A : Type u} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Regard a finite probability vector as a constant kernel from a singleton input. -/
noncomputable def ofProbabilityVector (law : ProbabilityVector A) :
    SingletonMarkovKernel A :=
  ⟨Kernel.const Unit law.toPMF.toMeasure, inferInstance⟩

/-- Recover the finite probability vector carried by a singleton-input Markov kernel. -/
noncomputable def toProbabilityVector (kernel : SingletonMarkovKernel A) :
    ProbabilityVector A := by
  letI : IsMarkovKernel kernel.1 := kernel.2
  letI : IsProbabilityMeasure (kernel.1 ()) :=
    IsMarkovKernel.isProbabilityMeasure ()
  exact ProbabilityVector.ofPMF ((kernel.1 ()).toPMF)

/-- Recovering a law from its singleton kernel returns the original probability vector. -/
@[simp]
theorem toProbabilityVector_ofProbabilityVector (law : ProbabilityVector A) :
    toProbabilityVector (ofProbabilityVector law) = law := by
  apply ProbabilityVector.ext
  intro a
  change ((Kernel.const Unit law.toPMF.toMeasure) () {a}).toReal = law a
  rw [Kernel.const_apply,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  exact ENNReal.toReal_ofReal (law.nonneg a)

/-- Re-encoding a singleton kernel from its recovered law returns the original kernel. -/
@[simp]
theorem ofProbabilityVector_toProbabilityVector (kernel : SingletonMarkovKernel A) :
    ofProbabilityVector (toProbabilityVector kernel) = kernel := by
  apply Subtype.ext
  apply Kernel.ext
  intro input
  cases input
  simp only [ofProbabilityVector, Kernel.const_apply]
  let : IsMarkovKernel kernel.1 := kernel.2
  let : IsProbabilityMeasure (kernel.1 ()) :=
    IsMarkovKernel.isProbabilityMeasure ()
  unfold toProbabilityVector
  rw [ProbabilityVector.toPMF_ofPMF]
  exact Measure.toPMF_toMeasure (kernel.1 ())

/-- Finite probability vectors are equivalent to singleton-input measure-theoretic kernels. -/
noncomputable def probabilityVectorEquiv :
    ProbabilityVector A ≃ SingletonMarkovKernel A where
  toFun := ofProbabilityVector
  invFun := toProbabilityVector
  left_inv := toProbabilityVector_ofProbabilityVector
  right_inv := ofProbabilityVector_toProbabilityVector

end SingletonMarkovKernel

end FiniteMarkovKernels
