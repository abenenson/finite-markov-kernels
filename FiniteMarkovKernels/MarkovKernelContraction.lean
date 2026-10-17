/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import FiniteMarkovKernels.ProbabilityVector

/-!
# Total-variation contraction for finite Markov kernels

This file defines total variation on finite probability vectors and the action and temporal
composition of finite stochastic kernels.

## Main Results

- `ProbabilityVector.totalVariation_eq_zero_iff`.
- `ProbabilityVector.totalVariation_triangle`.
- `FiniteMarkovKernel.apply`.
- `FiniteMarkovKernel.apply_followedBy`.
- `FiniteMarkovKernel.followedBy_assoc`.
- `FiniteMarkovKernel.iterate_add`.
- `FiniteMarkovKernel.iterate_iterate`.
- `FiniteMarkovKernel.totalVariation_apply_le`.
- `FiniteMarkovKernel.totalVariation_apply_le_contractionCoefficient`.
- `FiniteMarkovKernel.contractionCoefficient_followedBy_le`.
- `FiniteMarkovKernel.contractionCoefficient_relabelInput`.
- `FiniteMarkovKernel.contractionCoefficient_relabelOutput`.
- `FiniteMarkovKernel.contractionCoefficient_iterate_le`.
- `FiniteMarkovKernel.totalVariation_iterate_le`.
- `FiniteMarkovKernel.exists_strict_contractionCoefficient_followedBy`.
-/

namespace FiniteMarkovKernels

open scoped BigOperators

universe u v w x

namespace ProbabilityVector

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

/-- Total-variation distance on a finite probability simplex. -/
noncomputable def totalVariation (p q : ProbabilityVector A) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |p a - q a|

/-- Total variation is nonnegative. -/
theorem totalVariation_nonneg (p q : ProbabilityVector A) :
    0 ≤ totalVariation p q := by
  unfold totalVariation
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ha ↦ abs_nonneg (p a - q a))

/-- A probability vector has zero total variation from itself. -/
@[simp]
theorem totalVariation_self (p : ProbabilityVector A) :
    totalVariation p p = 0 := by
  simp [totalVariation]

/-- Total variation is symmetric. -/
theorem totalVariation_comm (p q : ProbabilityVector A) :
    totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

/-- Total variation satisfies the triangle inequality. -/
theorem totalVariation_triangle (p q r : ProbabilityVector A) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  unfold totalVariation
  rw [← mul_add, ← Finset.sum_add_distrib]
  gcongr with a
  calc
    |p a - r a| = |(p a - q a) + (q a - r a)| := by ring_nf
    _ ≤ |p a - q a| + |q a - r a| := abs_add_le _ _

/-- Total variation vanishes exactly on equal probability vectors. -/
@[simp]
theorem totalVariation_eq_zero_iff (p q : ProbabilityVector A) :
    totalVariation p q = 0 ↔ p = q := by
  constructor
  · intro hzero
    have hsum : ∑ a, |p a - q a| = 0 := by
      unfold totalVariation at hzero
      linarith
    apply ProbabilityVector.ext
    intro a
    have hall :
        (fun x ↦ |p x - q x|) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg fun x ↦ abs_nonneg (p x - q x)).mp hsum
    have habs : |p a - q a| = 0 := by
      simpa using congrFun hall a
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · rintro rfl
    exact totalVariation_self p

/-- Total variation is at most one on probability vectors. -/
theorem totalVariation_le_one (p q : ProbabilityVector A) :
    totalVariation p q ≤ 1 := by
  have hcoordinate (a : A) : |p a - q a| ≤ p a + q a := by
    calc
      |p a - q a| ≤ |p a| + |q a| := abs_sub _ _
      _ = p a + q a := by rw [abs_of_nonneg (p.nonneg a), abs_of_nonneg (q.nonneg a)]
  calc
    totalVariation p q ≤ (1 / 2 : ℝ) * ∑ a, (p a + q a) := by
      unfold totalVariation
      gcongr with a
      exact hcoordinate a
    _ = 1 := by rw [Finset.sum_add_distrib, p.sum_eq_one, q.sum_eq_one]; norm_num

/-- Simultaneous relabelling preserves finite total variation. -/
theorem totalVariation_relabel (e : A ≃ B) (p q : ProbabilityVector A) :
    totalVariation (relabel e p) (relabel e q) = totalVariation p q := by
  unfold totalVariation
  congr 1
  exact Fintype.sum_equiv e.symm _ _ fun b ↦ by simp

/-- Distinct point masses have total-variation distance one. -/
@[simp]
theorem totalVariation_dirac [DecidableEq A] (a a' : A) :
    totalVariation (dirac a) (dirac a') = if a = a' then 0 else 1 := by
  by_cases haa' : a = a'
  · simp [haa']
  · unfold totalVariation
    have hcoordinate (x : A) :
        |dirac a x - dirac a' x| =
          if x = a then 1 else if x = a' then 1 else 0 := by
      by_cases hxa : x = a
      · subst x
        simp [dirac_apply, haa']
      · by_cases hxa' : x = a'
        · subst x
          simp [dirac_apply, hxa]
        · simp [dirac_apply, hxa, hxa']
    have hseparate (x : A) :
        (if x = a then (1 : ℝ) else if x = a' then 1 else 0) =
          (if x = a then 1 else 0) + (if x = a' then 1 else 0) := by
      by_cases hxa : x = a
      · subst x
        simp [haa']
      · simp [hxa]
    simp_rw [hcoordinate]
    simp_rw [hseparate]
    rw [Finset.sum_add_distrib]
    simp [haa']
    norm_num

/-- On a binary probability simplex, total variation is one coordinate's absolute difference. -/
theorem totalVariation_finTwo (p q : ProbabilityVector (Fin 2)) :
    totalVariation p q = |p 1 - q 1| := by
  have hp : p 0 + p 1 = 1 := by
    simpa only [Fin.sum_univ_two] using p.sum_eq_one
  have hq : q 0 + q 1 = 1 := by
    simpa only [Fin.sum_univ_two] using q.sum_eq_one
  have hzero : p 0 - q 0 = -(p 1 - q 1) := by
    linarith
  unfold totalVariation
  rw [Fin.sum_univ_two, hzero, abs_neg]
  ring

end ProbabilityVector

/-- A finite Markov kernel assigns one finite probability vector to each input state. -/
abbrev FiniteMarkovKernel (A : Type u) (B : Type v) [Fintype B] :=
  A → ProbabilityVector B

namespace FiniteMarkovKernel

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- Push a finite input law through a finite Markov kernel. -/
noncomputable def apply (kernel : FiniteMarkovKernel A B) (law : ProbabilityVector A) :
    ProbabilityVector B where
  prob b := ∑ a, law a * kernel a b
  nonneg b := Finset.sum_nonneg fun a _ ↦ mul_nonneg (law.nonneg a) ((kernel a).nonneg b)
  sum_eq_one := by
    rw [Finset.sum_comm]
    calc
      (∑ a, ∑ b, law a * kernel a b) = ∑ a, law a * ∑ b, kernel a b := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = ∑ a, law a := by simp only [(kernel _).sum_eq_one, mul_one]
      _ = 1 := law.sum_eq_one

/-- Evaluating a kernel-applied law is the finite input-weighted sum of its rows. -/
@[simp]
theorem apply_prob (kernel : FiniteMarkovKernel A B) (law : ProbabilityVector A) (b : B) :
    kernel.apply law b = ∑ a, law a * kernel a b :=
  rfl

/-- Temporal composition: first apply `kernel`, then apply `later`. -/
noncomputable def followedBy (kernel : FiniteMarkovKernel A B)
    (later : FiniteMarkovKernel B C) : FiniteMarkovKernel A C :=
  fun a ↦ later.apply (kernel a)

omit [Fintype A] in
/-- Evaluating a temporal composite is the finite intermediate-state weighted sum. -/
@[simp]
theorem followedBy_prob (kernel : FiniteMarkovKernel A B)
    (later : FiniteMarkovKernel B C) (a : A) (c : C) :
    kernel.followedBy later a c = ∑ b, kernel a b * later b c :=
  rfl

/-- Applying a temporal composite is successive kernel application. -/
theorem apply_followedBy (kernel : FiniteMarkovKernel A B)
    (later : FiniteMarkovKernel B C) (law : ProbabilityVector A) :
    (kernel.followedBy later).apply law = later.apply (kernel.apply law) := by
  apply ProbabilityVector.ext
  intro c
  simp only [apply_prob, followedBy_prob]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

omit [Fintype A] in
/-- Temporal composition of finite Markov kernels is associative. -/
theorem followedBy_assoc (kernel : FiniteMarkovKernel A B)
    (middle : FiniteMarkovKernel B C) (later : FiniteMarkovKernel C D) :
    (kernel.followedBy middle).followedBy later =
      kernel.followedBy (middle.followedBy later) := by
  funext a
  exact (apply_followedBy middle later (kernel a)).symm

/-- The identity finite Markov kernel. -/
noncomputable def identity [DecidableEq A] : FiniteMarkovKernel A A :=
  ProbabilityVector.dirac

/-- Applying the identity kernel leaves a probability vector unchanged. -/
@[simp]
theorem identity_apply [DecidableEq A] (law : ProbabilityVector A) :
    identity.apply law = law := by
  apply ProbabilityVector.ext
  intro a
  simp [identity, apply_prob, ProbabilityVector.dirac_apply]

/-- A constant finite Markov kernel ignores its input. -/
def constant (law : ProbabilityVector B) : FiniteMarkovKernel A B :=
  fun _ ↦ law

/-- Applying a constant kernel produces its fixed output law. -/
@[simp]
theorem constant_apply (output : ProbabilityVector B) (law : ProbabilityVector A) :
    (constant output).apply law = output := by
  apply ProbabilityVector.ext
  intro b
  simp only [apply_prob, constant]
  rw [← Finset.sum_mul, law.sum_eq_one, one_mul]

/-- Applying a finite kernel to a point mass selects the corresponding kernel row. -/
@[simp]
theorem apply_dirac [DecidableEq A] (kernel : FiniteMarkovKernel A B) (a : A) :
    kernel.apply (ProbabilityVector.dirac a) = kernel a := by
  apply ProbabilityVector.ext
  intro b
  simp only [apply_prob, ProbabilityVector.dirac_apply]
  calc
    (∑ x, (if x = a then (1 : ℝ) else 0) * kernel x b) =
        (if a = a then (1 : ℝ) else 0) * kernel a b := by
      apply Finset.sum_eq_single a
      · intro x _hx hxa
        simp [hxa]
      · simp
    _ = kernel a b := by simp

/-- The identity kernel is a left identity for temporal composition. -/
@[simp]
theorem identity_followedBy [DecidableEq A] (kernel : FiniteMarkovKernel A B) :
    (identity : FiniteMarkovKernel A A).followedBy kernel = kernel := by
  funext a
  exact apply_dirac kernel a

omit [Fintype A] in
/-- The identity kernel is a right identity for temporal composition. -/
@[simp]
theorem followedBy_identity [DecidableEq B] (kernel : FiniteMarkovKernel A B) :
    kernel.followedBy identity = kernel := by
  funext a
  exact identity_apply (kernel a)

/-- A deterministic finite Markov kernel induced by a function. -/
noncomputable def deterministic [DecidableEq B] (f : A → B) :
    FiniteMarkovKernel A B :=
  fun a ↦ ProbabilityVector.dirac (f a)

/-- A deterministic kernel sends a point mass to the corresponding point mass. -/
@[simp 1100]
theorem deterministic_apply_dirac [DecidableEq A] [DecidableEq B]
    (f : A → B) (a : A) :
    (deterministic f).apply (ProbabilityVector.dirac a) =
      ProbabilityVector.dirac (f a) :=
  apply_dirac (deterministic f) a

/-- Relabel the output alphabet of a finite Markov kernel. -/
noncomputable def relabelOutput (e : B ≃ C) (kernel : FiniteMarkovKernel A B) :
    FiniteMarkovKernel A C :=
  fun a ↦ ProbabilityVector.relabel e (kernel a)

/-- Output relabeling commutes with application of a finite kernel. -/
theorem relabelOutput_apply (e : B ≃ C) (kernel : FiniteMarkovKernel A B)
    (law : ProbabilityVector A) :
    (relabelOutput e kernel).apply law =
      ProbabilityVector.relabel e (kernel.apply law) := by
  apply ProbabilityVector.ext
  intro c
  simp only [apply_prob, relabelOutput, ProbabilityVector.relabel_apply]

/-- Relabel the input alphabet of a finite Markov kernel. -/
def relabelInput (e : A ≃ B) (kernel : FiniteMarkovKernel A C) :
    FiniteMarkovKernel B C :=
  fun b ↦ kernel (e.symm b)

/-- Input relabeling cancels transport of the input probability vector. -/
theorem relabelInput_apply (e : A ≃ B) (kernel : FiniteMarkovKernel A C)
    (law : ProbabilityVector A) :
    (relabelInput e kernel).apply (ProbabilityVector.relabel e law) =
      kernel.apply law := by
  apply ProbabilityVector.ext
  intro c
  simp only [apply_prob, relabelInput, ProbabilityVector.relabel_apply]
  exact Fintype.sum_equiv e.symm _ _ fun b ↦ by simp

omit [Fintype A] in
/-- Relabeling an internal alphabet cancels across temporal composition. -/
theorem relabelOutput_followedBy_relabelInput (e : B ≃ C)
    (kernel : FiniteMarkovKernel A B) (later : FiniteMarkovKernel B D) :
    (relabelOutput e kernel).followedBy (relabelInput e later) =
      kernel.followedBy later := by
  funext a
  exact relabelInput_apply e later (kernel a)

omit [Fintype A] [Fintype B] in
/-- Input relabeling commutes with temporal composition. -/
theorem relabelInput_followedBy (e : A ≃ B)
    (kernel : FiniteMarkovKernel A C) (later : FiniteMarkovKernel C D) :
    relabelInput e (kernel.followedBy later) =
      (relabelInput e kernel).followedBy later :=
  rfl

omit [Fintype A] in
/-- Output relabeling commutes with temporal composition. -/
theorem followedBy_relabelOutput (e : C ≃ D)
    (kernel : FiniteMarkovKernel A B) (later : FiniteMarkovKernel B C) :
    relabelOutput e (kernel.followedBy later) =
      kernel.followedBy (relabelOutput e later) := by
  funext a
  exact (relabelOutput_apply e later (kernel a)).symm

omit [Fintype A] in
/-- Temporal composition of deterministic kernels is function composition. -/
theorem deterministic_followedBy [DecidableEq B] [DecidableEq C]
    (f : A → B) (g : B → C) :
    (deterministic f).followedBy (deterministic g) =
      deterministic (g ∘ f) := by
  funext a
  exact deterministic_apply_dirac g (f a)

/-- Homogeneous temporal iteration of an endomorphic finite Markov kernel. -/
noncomputable def iterate [DecidableEq A] (kernel : FiniteMarkovKernel A A) :
    ℕ → FiniteMarkovKernel A A
  | 0 => identity
  | n + 1 => (iterate kernel n).followedBy kernel

/-- Zero temporal iterations give the identity kernel. -/
@[simp]
theorem iterate_zero [DecidableEq A] (kernel : FiniteMarkovKernel A A) :
    iterate kernel 0 = identity :=
  rfl

/-- A successor iterate composes the preceding iterate with one further kernel. -/
@[simp]
theorem iterate_succ [DecidableEq A] (kernel : FiniteMarkovKernel A A) (n : ℕ) :
    iterate kernel (n + 1) = (iterate kernel n).followedBy kernel :=
  rfl

/-- Zero kernel iterations leave an input probability vector unchanged. -/
@[simp↓]
theorem iterate_zero_apply [DecidableEq A]
    (kernel : FiniteMarkovKernel A A) (law : ProbabilityVector A) :
    (iterate kernel 0).apply law = law :=
  identity_apply law

/-- A successor kernel iteration applies one further copy after the preceding iterations. -/
theorem iterate_succ_apply [DecidableEq A]
    (kernel : FiniteMarkovKernel A A) (n : ℕ) (law : ProbabilityVector A) :
    (iterate kernel (n + 1)).apply law =
      kernel.apply ((iterate kernel n).apply law) :=
  apply_followedBy _ _ _

/-- Iteration at a sum is temporal composition of the corresponding iterates. -/
theorem iterate_add [DecidableEq A] (kernel : FiniteMarkovKernel A A) (m n : ℕ) :
    iterate kernel (m + n) = (iterate kernel m).followedBy (iterate kernel n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_succ, iterate_succ, ih, iterate_succ, followedBy_assoc]

/-- Iterating an iterated kernel multiplies the two temporal depths. -/
theorem iterate_iterate [DecidableEq A]
    (kernel : FiniteMarkovKernel A A) (block n : ℕ) :
    iterate (iterate kernel block) n = iterate kernel (block * n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [iterate_succ, ih, Nat.mul_succ, iterate_add]

/-- Total variation cannot increase under a finite Markov kernel. -/
theorem totalVariation_apply_le (kernel : FiniteMarkovKernel A B)
    (p q : ProbabilityVector A) :
    ProbabilityVector.totalVariation (kernel.apply p) (kernel.apply q) ≤
      ProbabilityVector.totalVariation p q := by
  have hrewrite (b : B) :
      (∑ a, p a * kernel a b) - ∑ a, q a * kernel a b =
        ∑ a, (p a - q a) * kernel a b := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  have habs (b : B) :
      |∑ a, (p a - q a) * kernel a b| ≤
        ∑ a, |p a - q a| * kernel a b := by
    calc
      |∑ a, (p a - q a) * kernel a b| ≤
          ∑ a, |(p a - q a) * kernel a b| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, |p a - q a| * kernel a b := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [abs_mul, abs_of_nonneg ((kernel a).nonneg b)]
  unfold ProbabilityVector.totalVariation
  simp only [apply_prob, hrewrite]
  calc
    (1 / 2 : ℝ) * ∑ b, |∑ a, (p a - q a) * kernel a b| ≤
        (1 / 2 : ℝ) * ∑ b, ∑ a, |p a - q a| * kernel a b := by
      gcongr with b
      exact habs b
    _ = (1 / 2 : ℝ) * ∑ a, |p a - q a| := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [← Finset.mul_sum, (kernel a).sum_eq_one, mul_one]

/-- The total-variation contraction ratio for a particular pair of input laws.

The ratio is defined to be zero when the input laws coincide. -/
noncomputable def contractionRatio (kernel : FiniteMarkovKernel A B)
    (p q : ProbabilityVector A) : ℝ :=
  if ProbabilityVector.totalVariation p q = 0 then 0
  else
    ProbabilityVector.totalVariation (kernel.apply p) (kernel.apply q) /
      ProbabilityVector.totalVariation p q

/-- A finite kernel's worst-case total-variation contraction ratio. -/
noncomputable def contractionCoefficient (kernel : FiniteMarkovKernel A B) : ℝ :=
  sSup (Set.range fun pair : ProbabilityVector A × ProbabilityVector A ↦
    contractionRatio kernel pair.1 pair.2)

/-- Every total-variation contraction ratio is nonnegative. -/
theorem contractionRatio_nonneg (kernel : FiniteMarkovKernel A B)
    (p q : ProbabilityVector A) :
    0 ≤ contractionRatio kernel p q := by
  unfold contractionRatio
  split_ifs
  · exact le_rfl
  · exact div_nonneg
      (ProbabilityVector.totalVariation_nonneg _ _)
      (ProbabilityVector.totalVariation_nonneg _ _)

/-- Every total-variation contraction ratio is at most one. -/
theorem contractionRatio_le_one (kernel : FiniteMarkovKernel A B)
    (p q : ProbabilityVector A) :
    contractionRatio kernel p q ≤ 1 := by
  unfold contractionRatio
  split_ifs with hzero
  · norm_num
  · have hpositive : 0 < ProbabilityVector.totalVariation p q :=
      lt_of_le_of_ne (ProbabilityVector.totalVariation_nonneg p q) (Ne.symm hzero)
    apply (div_le_one hpositive).2
    exact totalVariation_apply_le kernel p q

private theorem contractionRatio_range_bddAbove (kernel : FiniteMarkovKernel A B) :
    BddAbove (Set.range fun pair : ProbabilityVector A × ProbabilityVector A ↦
      contractionRatio kernel pair.1 pair.2) :=
  ⟨1, Set.forall_mem_range.2 fun pair ↦ contractionRatio_le_one kernel pair.1 pair.2⟩

/-- A pair's contraction ratio is bounded by the kernel's coefficient. -/
theorem contractionRatio_le_contractionCoefficient [Nonempty A]
    (kernel : FiniteMarkovKernel A B) (p q : ProbabilityVector A) :
    contractionRatio kernel p q ≤ contractionCoefficient kernel := by
  rcases ‹Nonempty A› with ⟨_a⟩
  apply le_csSup (contractionRatio_range_bddAbove kernel)
  exact ⟨(p, q), rfl⟩

/-- The contraction coefficient is below every global contraction-ratio bound. -/
theorem contractionCoefficient_le_of_ratio_le [Nonempty A]
    (kernel : FiniteMarkovKernel A B) {bound : ℝ}
    (hbound : ∀ p q, contractionRatio kernel p q ≤ bound) :
    contractionCoefficient kernel ≤ bound := by
  classical
  let law : ProbabilityVector A :=
    ProbabilityVector.dirac (Classical.arbitrary A)
  apply csSup_le
  · exact ⟨contractionRatio kernel law law, ⟨(law, law), rfl⟩⟩
  · rintro _ ⟨pair, rfl⟩
    exact hbound pair.1 pair.2

/-- A finite kernel's contraction coefficient is nonnegative. -/
theorem contractionCoefficient_nonneg [Nonempty A]
    (kernel : FiniteMarkovKernel A B) :
    0 ≤ contractionCoefficient kernel := by
  classical
  let law : ProbabilityVector A :=
    ProbabilityVector.dirac (Classical.arbitrary A)
  exact
    (contractionRatio_nonneg kernel law law).trans
      (contractionRatio_le_contractionCoefficient kernel law law)

/-- A finite kernel's contraction coefficient is at most one. -/
theorem contractionCoefficient_le_one [Nonempty A]
    (kernel : FiniteMarkovKernel A B) :
    contractionCoefficient kernel ≤ 1 := by
  classical
  let law : ProbabilityVector A :=
    ProbabilityVector.dirac (Classical.arbitrary A)
  apply csSup_le
  · exact ⟨contractionRatio kernel law law, ⟨(law, law), rfl⟩⟩
  · rintro _ ⟨pair, rfl⟩
    exact contractionRatio_le_one kernel pair.1 pair.2

/-- A finite kernel contracts total variation by at most its contraction coefficient. -/
theorem totalVariation_apply_le_contractionCoefficient [Nonempty A]
    (kernel : FiniteMarkovKernel A B) (p q : ProbabilityVector A) :
    ProbabilityVector.totalVariation (kernel.apply p) (kernel.apply q) ≤
      contractionCoefficient kernel * ProbabilityVector.totalVariation p q := by
  by_cases hzero : ProbabilityVector.totalVariation p q = 0
  · have hpq : p = q := (ProbabilityVector.totalVariation_eq_zero_iff p q).mp hzero
    simp [hpq]
  · have hpositive : 0 < ProbabilityVector.totalVariation p q :=
      lt_of_le_of_ne (ProbabilityVector.totalVariation_nonneg p q) (Ne.symm hzero)
    have hratio :=
      contractionRatio_le_contractionCoefficient kernel p q
    rw [contractionRatio, ite_eq_right hzero] at hratio
    exact (div_le_iff₀ hpositive).mp hratio

/-- Contraction coefficients are submultiplicative under temporal composition. -/
theorem contractionCoefficient_followedBy_le [Nonempty A] [Nonempty B]
    (kernel : FiniteMarkovKernel A B) (later : FiniteMarkovKernel B C) :
    contractionCoefficient (kernel.followedBy later) ≤
      contractionCoefficient kernel * contractionCoefficient later := by
  classical
  let law : ProbabilityVector A :=
    ProbabilityVector.dirac (Classical.arbitrary A)
  apply csSup_le
  · exact ⟨contractionRatio (kernel.followedBy later) law law, ⟨(law, law), rfl⟩⟩
  · rintro _ ⟨pair, rfl⟩
    rcases pair with ⟨p, q⟩
    change contractionRatio (kernel.followedBy later) p q ≤
      contractionCoefficient kernel * contractionCoefficient later
    unfold contractionRatio
    split_ifs with hzero
    · exact mul_nonneg
        (contractionCoefficient_nonneg kernel)
        (contractionCoefficient_nonneg later)
    · have hpositive : 0 < ProbabilityVector.totalVariation p q :=
        lt_of_le_of_ne (ProbabilityVector.totalVariation_nonneg p q) (Ne.symm hzero)
      apply (div_le_iff₀ hpositive).2
      simp only [apply_followedBy]
      calc
        ProbabilityVector.totalVariation
              (later.apply (kernel.apply p)) (later.apply (kernel.apply q)) ≤
            contractionCoefficient later *
              ProbabilityVector.totalVariation (kernel.apply p) (kernel.apply q) :=
          totalVariation_apply_le_contractionCoefficient later _ _
        _ ≤ contractionCoefficient later *
              (contractionCoefficient kernel * ProbabilityVector.totalVariation p q) := by
          exact mul_le_mul_of_nonneg_left
            (totalVariation_apply_le_contractionCoefficient kernel p q)
            (contractionCoefficient_nonneg later)
        _ = (contractionCoefficient kernel * contractionCoefficient later) *
              ProbabilityVector.totalVariation p q := by ring

/-- The coefficient of an iterated kernel is bounded by the corresponding coefficient power. -/
theorem contractionCoefficient_iterate_le [Nonempty A] [DecidableEq A]
    (kernel : FiniteMarkovKernel A A) (n : ℕ) :
    contractionCoefficient (iterate kernel n) ≤ contractionCoefficient kernel ^ n := by
  induction n with
  | zero =>
      simpa only [iterate_zero, pow_zero] using
        contractionCoefficient_le_one (identity : FiniteMarkovKernel A A)
  | succ n ih =>
      calc
        contractionCoefficient (iterate kernel (n + 1)) ≤
            contractionCoefficient (iterate kernel n) * contractionCoefficient kernel := by
          rw [iterate_succ]
          exact contractionCoefficient_followedBy_le _ _
        _ ≤ contractionCoefficient kernel ^ n * contractionCoefficient kernel :=
          mul_le_mul_of_nonneg_right ih (contractionCoefficient_nonneg kernel)
        _ = contractionCoefficient kernel ^ (n + 1) := (pow_succ _ n).symm

/-- Iterated application contracts total variation by the coefficient power. -/
theorem totalVariation_iterate_le [Nonempty A] [DecidableEq A]
    (kernel : FiniteMarkovKernel A A) (n : ℕ) (p q : ProbabilityVector A) :
    ProbabilityVector.totalVariation
        ((iterate kernel n).apply p) ((iterate kernel n).apply q) ≤
      contractionCoefficient kernel ^ n * ProbabilityVector.totalVariation p q := by
  calc
    ProbabilityVector.totalVariation
          ((iterate kernel n).apply p) ((iterate kernel n).apply q) ≤
        contractionCoefficient (iterate kernel n) *
          ProbabilityVector.totalVariation p q :=
      totalVariation_apply_le_contractionCoefficient (iterate kernel n) p q
    _ ≤ contractionCoefficient kernel ^ n * ProbabilityVector.totalVariation p q :=
      mul_le_mul_of_nonneg_right
        (contractionCoefficient_iterate_le kernel n)
        (ProbabilityVector.totalVariation_nonneg p q)

/-- Output relabeling preserves every contraction ratio. -/
theorem contractionRatio_relabelOutput (e : B ≃ C)
    (kernel : FiniteMarkovKernel A B) (p q : ProbabilityVector A) :
    contractionRatio (relabelOutput e kernel) p q =
      contractionRatio kernel p q := by
  unfold contractionRatio
  simp only [relabelOutput_apply, ProbabilityVector.totalVariation_relabel]

/-- Transporting input laws along an input relabeling preserves contraction ratios. -/
theorem contractionRatio_relabelInput (e : A ≃ B)
    (kernel : FiniteMarkovKernel A C) (p q : ProbabilityVector A) :
    contractionRatio (relabelInput e kernel)
        (ProbabilityVector.relabel e p) (ProbabilityVector.relabel e q) =
      contractionRatio kernel p q := by
  unfold contractionRatio
  simp only [relabelInput_apply, ProbabilityVector.totalVariation_relabel]

/-- Output relabeling preserves the contraction coefficient. -/
theorem contractionCoefficient_relabelOutput (e : B ≃ C)
    (kernel : FiniteMarkovKernel A B) :
    contractionCoefficient (relabelOutput e kernel) =
      contractionCoefficient kernel := by
  unfold contractionCoefficient
  simp_rw [contractionRatio_relabelOutput]

/-- Input relabeling preserves the contraction coefficient. -/
theorem contractionCoefficient_relabelInput (e : A ≃ B)
    (kernel : FiniteMarkovKernel A C) :
    contractionCoefficient (relabelInput e kernel) =
      contractionCoefficient kernel := by
  unfold contractionCoefficient
  congr 1
  ext ratio
  constructor
  · rintro ⟨pair, rfl⟩
    let p := ProbabilityVector.relabel e.symm pair.1
    let q := ProbabilityVector.relabel e.symm pair.2
    have hp : ProbabilityVector.relabel e p = pair.1 := by
      simpa [p] using ProbabilityVector.relabel_symm_relabel e.symm pair.1
    have hq : ProbabilityVector.relabel e q = pair.2 := by
      simpa [q] using ProbabilityVector.relabel_symm_relabel e.symm pair.2
    refine ⟨(p, q), ?_⟩
    change contractionRatio kernel p q =
      contractionRatio (relabelInput e kernel) pair.1 pair.2
    rw [← hp, ← hq]
    exact (contractionRatio_relabelInput e kernel p q).symm
  · rintro ⟨pair, rfl⟩
    refine ⟨(ProbabilityVector.relabel e pair.1,
      ProbabilityVector.relabel e pair.2), ?_⟩
    change contractionRatio (relabelInput e kernel)
        (ProbabilityVector.relabel e pair.1)
        (ProbabilityVector.relabel e pair.2) =
      contractionRatio kernel pair.1 pair.2
    exact contractionRatio_relabelInput e kernel pair.1 pair.2

/-- Every input pair has zero contraction ratio under a constant kernel. -/
@[simp]
theorem contractionRatio_constant (output : ProbabilityVector B)
    (p q : ProbabilityVector A) :
    contractionRatio (constant output) p q = 0 := by
  simp [contractionRatio]

/-- A constant kernel has contraction coefficient zero. -/
@[simp]
theorem contractionCoefficient_constant [Nonempty A]
    (output : ProbabilityVector B) :
    contractionCoefficient (constant output : FiniteMarkovKernel A B) = 0 := by
  classical
  let law : ProbabilityVector A :=
    ProbabilityVector.dirac (Classical.arbitrary A)
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, ⟨(law, law), by simp⟩⟩
    · rintro _ ⟨pair, rfl⟩
      exact le_of_eq (contractionRatio_constant output pair.1 pair.2)
  · exact contractionCoefficient_nonneg _

/-- The identity kernel on a nontrivial alphabet has contraction coefficient one. -/
@[simp]
theorem contractionCoefficient_identity [Nontrivial A] [DecidableEq A] :
    contractionCoefficient (identity : FiniteMarkovKernel A A) = 1 := by
  classical
  apply le_antisymm (contractionCoefficient_le_one identity)
  obtain ⟨a, a', haa'⟩ := exists_pair_ne A
  have hratio :
      contractionRatio identity
          (ProbabilityVector.dirac a) (ProbabilityVector.dirac a') = 1 := by
    simp [contractionRatio, identity, haa']
  rw [← hratio]
  exact contractionRatio_le_contractionCoefficient identity _ _

/-- Left composition by identity attains the coefficient composition bound. -/
theorem contractionCoefficient_identity_followedBy [Nontrivial A] [DecidableEq A]
    (kernel : FiniteMarkovKernel A B) :
    contractionCoefficient
        ((identity : FiniteMarkovKernel A A).followedBy kernel) =
      contractionCoefficient (identity : FiniteMarkovKernel A A) *
        contractionCoefficient kernel := by
  rw [identity_followedBy, contractionCoefficient_identity, one_mul]

/-- The identity kernel on a singleton alphabet has contraction coefficient zero. -/
@[simp]
theorem contractionCoefficient_identity_of_subsingleton [Subsingleton A]
    [Nonempty A] [DecidableEq A] :
    contractionCoefficient (identity : FiniteMarkovKernel A A) = 0 := by
  let output := ProbabilityVector.dirac (Classical.arbitrary A)
  have hkernel :
      (identity : FiniteMarkovKernel A A) = constant output := by
    funext a
    apply ProbabilityVector.ext
    intro x
    have ha : a = Classical.arbitrary A := Subsingleton.elim _ _
    simp [identity, constant, output, ha]
  rw [hkernel, contractionCoefficient_constant]

/-- A deterministic kernel that separates two inputs has contraction coefficient one. -/
theorem contractionCoefficient_deterministic_of_ne [Nonempty A]
    [DecidableEq A] [DecidableEq B] {f : A → B} {a a' : A}
    (hseparate : f a ≠ f a') :
    contractionCoefficient (deterministic f) = 1 := by
  have haa' : a ≠ a' := fun haa' ↦ hseparate (congrArg f haa')
  apply le_antisymm (contractionCoefficient_le_one (deterministic f))
  have hratio :
      contractionRatio (deterministic f)
          (ProbabilityVector.dirac a) (ProbabilityVector.dirac a') = 1 := by
    simp [contractionRatio, haa', hseparate]
  rw [← hratio]
  exact contractionRatio_le_contractionCoefficient (deterministic f) _ _

/-- Two nonconstant deterministic stages can compose to a strictly contractive constant channel. -/
theorem contractionCoefficient_followedBy_lt_of_deterministic_collapse
    [Nonempty A] [Nonempty B] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {f : A → B} {g : B → C} {a a' : A} {b b' : B}
    (hf : f a ≠ f a') (hg : g b ≠ g b')
    (hcollapse : ∀ x y, g (f x) = g (f y)) :
    contractionCoefficient ((deterministic f).followedBy (deterministic g)) <
      contractionCoefficient (deterministic f) *
        contractionCoefficient (deterministic g) := by
  have hfirst := contractionCoefficient_deterministic_of_ne hf
  have hlater := contractionCoefficient_deterministic_of_ne hg
  let output := ProbabilityVector.dirac (g (f a))
  have hcomposite :
      (deterministic f).followedBy (deterministic g) =
        (constant output : FiniteMarkovKernel A C) := by
    rw [deterministic_followedBy]
    funext x
    apply ProbabilityVector.ext
    intro c
    simp [deterministic, constant, output, hcollapse x a]
  rw [hcomposite, contractionCoefficient_constant, hfirst, hlater]
  norm_num

/-- A binary--ternary--binary chain witnesses strict coefficient submultiplicativity. -/
theorem exists_strict_contractionCoefficient_followedBy :
    ∃ (kernel : FiniteMarkovKernel Bool (Option Bool))
      (later : FiniteMarkovKernel (Option Bool) Bool),
      contractionCoefficient (kernel.followedBy later) <
        contractionCoefficient kernel * contractionCoefficient later := by
  let f : Bool → Option Bool := some
  let g : Option Bool → Bool
    | none => true
    | some _ => false
  refine ⟨deterministic f, deterministic g, ?_⟩
  apply contractionCoefficient_followedBy_lt_of_deterministic_collapse
      (a := false) (a' := true) (b := none) (b' := some false)
  · simp [f]
  · simp [g]
  · intro x y
    simp [f, g]

end FiniteMarkovKernel

end FiniteMarkovKernels
