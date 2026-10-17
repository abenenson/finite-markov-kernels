/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Finite probability vectors with boundary

This file defines the closed probability simplex on an arbitrary finite type. Unlike the open
simplex commonly used in information geometry, zero coordinates are admitted. It also provides
relabeling and dependent block composition, the operations needed for finite relative-entropy
chain rules.

## Main results

- `ProbabilityVector`: nonnegative real weights summing to one.
- `ProbabilityVector.relabel`: transport along an equivalence of finite alphabets.
- `ProbabilityVector.compound`: dependent block composition on a sigma type.
- `ProbabilityVector.compound_absolutelyContinuous`: support transport through composition.
-/

namespace FiniteMarkovKernels

open scoped BigOperators

universe u v

/-- A probability distribution on a finite type, including boundary distributions with zeros. -/
structure ProbabilityVector (A : Type u) [Fintype A] where
  /-- Probability mass at each point. -/
  prob : A → ℝ
  /-- Every mass is nonnegative. -/
  nonneg : ∀ a, 0 ≤ prob a
  /-- Total mass is one. -/
  sum_eq_one : ∑ a, prob a = 1

namespace ProbabilityVector

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

instance : CoeFun (ProbabilityVector A) fun _ ↦ A → ℝ :=
  ⟨ProbabilityVector.prob⟩

/-- Probability vectors are equal when all their coordinates agree. -/
@[ext]
theorem ext {p q : ProbabilityVector A} (h : ∀ a, p a = q a) : p = q := by
  cases p
  cases q
  simp only [mk.injEq]
  funext a
  exact h a

attribute [inherit_doc FiniteMarkovKernels.ProbabilityVector.ext]
  FiniteMarkovKernels.ProbabilityVector.ext_iff

/-- The topology induced by the coordinate embedding into the finite function space. -/
instance : TopologicalSpace (ProbabilityVector A) :=
  TopologicalSpace.induced ProbabilityVector.prob inferInstance

/-- The Borel measurable space of the closed finite simplex. -/
instance : MeasurableSpace (ProbabilityVector A) :=
  borel (ProbabilityVector A)

/-- The simplex measurable space is the Borel measurable space of its coordinate topology. -/
instance : BorelSpace (ProbabilityVector A) :=
  ⟨rfl⟩

/-- The coordinate function of a probability vector is continuous. -/
theorem continuous_prob : Continuous fun p : ProbabilityVector A ↦ p.prob :=
  continuous_induced_dom

/-- Evaluation at one finite outcome is continuous on probability vectors. -/
theorem continuous_apply (a : A) : Continuous fun p : ProbabilityVector A ↦ p a :=
  (_root_.continuous_apply a).comp continuous_prob

/-- Evaluation at one finite outcome is measurable on probability vectors. -/
theorem measurable_apply (a : A) : Measurable fun p : ProbabilityVector A ↦ p a :=
  (continuous_apply a).measurable

/-- Simultaneous finite support condition corresponding to absolute continuity `p ≪ r`. -/
def AbsolutelyContinuous (p r : ProbabilityVector A) : Prop :=
  ∀ a, r a = 0 → p a = 0

/-- Every probability vector is absolutely continuous with respect to itself. -/
@[refl]
theorem absolutelyContinuous_refl (p : ProbabilityVector A) : AbsolutelyContinuous p p := by
  intro a ha
  exact ha

/-- Positive numerator mass forces positive reference mass under absolute continuity. -/
theorem pos_of_pos_of_absolutelyContinuous {p r : ProbabilityVector A}
    (hpr : AbsolutelyContinuous p r) {a : A} (hpa : 0 < p a) : 0 < r a := by
  exact lt_of_le_of_ne (r.nonneg a) fun hra ↦ hpa.ne' (hpr a hra.symm)

/-- Every coordinate of a probability vector is at most one. -/
theorem apply_le_one (p : ProbabilityVector A) (a : A) : p a ≤ 1 := by
  calc
    p a ≤ ∑ x, p x := Finset.single_le_sum (fun x _hx ↦ p.nonneg x) (Finset.mem_univ a)
    _ = 1 := p.sum_eq_one

/-- A finite probability vector has full support when every coordinate is strictly positive. -/
def FullSupport (p : ProbabilityVector A) : Prop :=
  ∀ a, 0 < p a

/-- Absolute continuity transports full support from the numerator to the reference. -/
theorem FullSupport.reference {p r : ProbabilityVector A} (hp : p.FullSupport)
    (hpr : AbsolutelyContinuous p r) : r.FullSupport :=
  fun a ↦ pos_of_pos_of_absolutelyContinuous hpr (hp a)

/-- The positive support of a finite probability vector. -/
abbrev Support (p : ProbabilityVector A) := {a : A // 0 < p a}

/-- The complement of the positive support of a finite probability vector. -/
abbrev SupportComplement (p : ProbabilityVector A) := {a : A // ¬0 < p a}

noncomputable instance supportFintype (p : ProbabilityVector A) : Fintype p.Support :=
  inferInstance

/-- A probability vector has nonempty positive support. -/
instance supportNonempty (p : ProbabilityVector A) : Nonempty p.Support := by
  classical
  have hexists : ∃ a, 0 < p a := by
    by_contra h
    push Not at h
    have hzero : ∀ a, p a = 0 := fun a ↦ le_antisymm (h a) (p.nonneg a)
    have : (∑ a, p a) = 0 := Finset.sum_eq_zero fun a _ha ↦ hzero a
    linarith [p.sum_eq_one]
  exact let ⟨a, ha⟩ := hexists; ⟨⟨a, ha⟩⟩

/-- Restrict a probability vector to its positive support. -/
noncomputable def onSupport (p : ProbabilityVector A) : ProbabilityVector p.Support where
  prob a := p a.1
  nonneg a := p.nonneg a.1
  sum_eq_one := by
    classical
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun a ↦ 0 < p a) fun a ↦ p a
    have hcompl : (∑ a : {a // ¬0 < p a}, p a) = 0 := by
      apply Finset.sum_eq_zero
      intro a _ha
      exact le_antisymm (not_lt.mp a.2) (p.nonneg a)
    linarith [p.sum_eq_one]

/-- Restricting to the positive support preserves the mass at each support point. -/
@[simp]
theorem onSupport_apply (p : ProbabilityVector A) (a : p.Support) : p.onSupport a = p a :=
  rfl

/-- Reference mass assigned to the positive support of `p`. -/
noncomputable def supportMass (p r : ProbabilityVector A) : ℝ :=
  ∑ a : p.Support, r a.1

/-- Reference mass outside the positive support of `p`. -/
noncomputable def supportComplementMass (p r : ProbabilityVector A) : ℝ :=
  ∑ a : p.SupportComplement, r a.1

/-- Reference mass splits across the support of `p` and its complement. -/
theorem supportMass_add_complementMass (p r : ProbabilityVector A) :
    supportMass p r + supportComplementMass p r = 1 := by
  classical
  exact (Fintype.sum_subtype_add_sum_subtype (fun a ↦ 0 < p a) fun a ↦ r a).trans
    r.sum_eq_one

/-- Reference mass on a support is at most one. -/
theorem supportMass_le_one (p r : ProbabilityVector A) : supportMass p r ≤ 1 := by
  have hnonneg : 0 ≤ supportComplementMass p r :=
    Finset.sum_nonneg fun a _ha ↦ r.nonneg a.1
  linarith [supportMass_add_complementMass p r]

/-- Absolute continuity makes the reference mass on the numerator support positive. -/
theorem supportMass_pos {p r : ProbabilityVector A} (hpr : AbsolutelyContinuous p r) :
    0 < supportMass p r := by
  classical
  let a : p.Support := Classical.choice inferInstance
  apply Finset.sum_pos'
  · intro x _hx
    exact r.nonneg x.1
  · exact ⟨a, Finset.mem_univ a, pos_of_pos_of_absolutelyContinuous hpr a.2⟩

/-- Normalize the reference distribution on the positive support of an absolutely continuous
numerator. -/
noncomputable def referenceOnSupport (p r : ProbabilityVector A)
    (hpr : AbsolutelyContinuous p r) : ProbabilityVector p.Support where
  prob a := r a.1 / supportMass p r
  nonneg a := div_nonneg (r.nonneg a.1) (supportMass_pos hpr).le
  sum_eq_one := by
    change (∑ a : p.Support, r a.1 * (supportMass p r)⁻¹) = 1
    rw [← Finset.sum_mul]
    change supportMass p r * (supportMass p r)⁻¹ = 1
    exact mul_inv_cancel₀ (supportMass_pos hpr).ne'

/-- The reference distribution on the numerator support is normalized by its support mass. -/
@[simp]
theorem referenceOnSupport_apply (p r : ProbabilityVector A)
    (hpr : AbsolutelyContinuous p r) (a : p.Support) :
    referenceOnSupport p r hpr a = r a.1 / supportMass p r :=
  rfl

/-- The support restrictions of an admissible pair remain admissible. -/
theorem onSupport_absolutelyContinuous {p r : ProbabilityVector A}
    (hpr : AbsolutelyContinuous p r) :
    AbsolutelyContinuous p.onSupport (referenceOnSupport p r hpr) := by
  intro a hra
  have hr : r a.1 = 0 := by
    simpa [referenceOnSupport_apply, (supportMass_pos hpr).ne'] using hra
  exact (a.2.ne' (hpr a.1 hr)).elim

/-- A normalized reference distribution on the complement of the numerator support. When that
complement has zero reference mass, an arbitrary point mass is used. -/
noncomputable def referenceOnSupportComplement (p r : ProbabilityVector A)
    [Nonempty p.SupportComplement] : ProbabilityVector p.SupportComplement := by
  classical
  exact if hzero : supportComplementMass p r = 0 then
      { prob := fun a ↦ if a = Classical.choice inferInstance then 1 else 0
        nonneg := fun a ↦ by positivity
        sum_eq_one := by simp }
    else
      { prob := fun a ↦ r a.1 / supportComplementMass p r
        nonneg := fun a ↦ div_nonneg (r.nonneg a.1) <|
          Finset.sum_nonneg fun x _hx ↦ r.nonneg x.1
        sum_eq_one := by
          change (∑ a : p.SupportComplement,
            r a.1 * (supportComplementMass p r)⁻¹) = 1
          rw [← Finset.sum_mul]
          change supportComplementMass p r * (supportComplementMass p r)⁻¹ = 1
          exact mul_inv_cancel₀ hzero }

/-- Scaling the normalized complement reference by its outer mass recovers each original
coordinate. -/
theorem supportComplementMass_mul_referenceOnSupportComplement
    (p r : ProbabilityVector A) [Nonempty p.SupportComplement]
    (a : p.SupportComplement) :
    (1 - supportMass p r) * referenceOnSupportComplement p r a = r a.1 := by
  have hmass : 1 - supportMass p r = supportComplementMass p r := by
    linarith [supportMass_add_complementMass p r]
  rw [hmass]
  by_cases hzero : supportComplementMass p r = 0
  · have hle : r a.1 ≤ supportComplementMass p r :=
      Finset.single_le_sum (fun x _hx ↦ r.nonneg x.1) (Finset.mem_univ a)
    have hra : r a.1 = 0 := le_antisymm (by simpa [hzero] using hle) (r.nonneg a.1)
    simp [referenceOnSupportComplement, hzero, hra]
  · simp only [referenceOnSupportComplement, hzero]
    exact mul_div_cancel₀ (r a.1) hzero

/-- Transport a probability vector along an equivalence of finite alphabets. -/
noncomputable def relabel (e : A ≃ B) (p : ProbabilityVector A) : ProbabilityVector B where
  prob b := p (e.symm b)
  nonneg b := p.nonneg (e.symm b)
  sum_eq_one := by
    calc
      (∑ b : B, p (e.symm b)) = ∑ a : A, p a := by
        symm
        exact Fintype.sum_equiv e _ _ fun a ↦ by simp
      _ = 1 := p.sum_eq_one

/-- Relabeling assigns each outcome the mass of its inverse image under the equivalence. -/
@[simp]
theorem relabel_apply (e : A ≃ B) (p : ProbabilityVector A) (b : B) :
    relabel e p b = p (e.symm b) :=
  rfl

/-- Relabeling by the identity equivalence leaves the probability vector unchanged. -/
@[simp]
theorem relabel_refl (p : ProbabilityVector A) : relabel (Equiv.refl A) p = p := by
  ext a
  rfl

/-- Relabeling by an equivalence and then its inverse recovers the original probability vector. -/
@[simp]
theorem relabel_symm_relabel (e : A ≃ B) (p : ProbabilityVector A) :
    relabel e.symm (relabel e p) = p := by
  ext a
  simp

/-- Absolute continuity is preserved by simultaneous relabeling. -/
theorem absolutelyContinuous_relabel_iff (e : A ≃ B) (p r : ProbabilityVector A) :
    AbsolutelyContinuous (relabel e p) (relabel e r) ↔ AbsolutelyContinuous p r := by
  constructor
  · intro h a hra
    have := h (e a) (by simpa using hra)
    simpa using this
  · intro h b hrb
    exact h (e.symm b) hrb

variable {C : A → Type v} [∀ a, Fintype (C a)]

/-- Dependent block composition: the mass at `(a,c)` is the outer mass at `a` times the inner
conditional mass at `c`. -/
noncomputable def compound (outer : ProbabilityVector A)
    (inner : ∀ a, ProbabilityVector (C a)) : ProbabilityVector (Σ a, C a) where
  prob z := outer z.1 * inner z.1 z.2
  nonneg z := mul_nonneg (outer.nonneg z.1) ((inner z.1).nonneg z.2)
  sum_eq_one := by
    rw [Fintype.sum_sigma]
    calc
      (∑ a, ∑ c, outer a * inner a c) = ∑ a, outer a * ∑ c, inner a c := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = ∑ a, outer a := by simp only [(inner _).sum_eq_one, mul_one]
      _ = 1 := outer.sum_eq_one

/-- A compound distribution assigns the outer mass times the corresponding conditional mass. -/
@[simp]
theorem compound_apply (outer : ProbabilityVector A) (inner : ∀ a, ProbabilityVector (C a))
    (a : A) (c : C a) :
    compound outer inner ⟨a, c⟩ = outer a * inner a c :=
  rfl

/-- Absolute continuity of outer and every inner pair implies absolute continuity of dependent
compound distributions. -/
theorem compound_absolutelyContinuous
    {outer referenceOuter : ProbabilityVector A}
    {inner referenceInner : ∀ a, ProbabilityVector (C a)}
    (hOuter : AbsolutelyContinuous outer referenceOuter)
    (hInner : ∀ a, AbsolutelyContinuous (inner a) (referenceInner a)) :
    AbsolutelyContinuous (compound outer inner) (compound referenceOuter referenceInner) := by
  rintro ⟨a, c⟩ hzero
  simp only [compound_apply] at hzero ⊢
  rcases mul_eq_zero.mp hzero with ha | hc
  · rw [hOuter a ha, zero_mul]
  · rw [hInner a c hc, mul_zero]

/-- The point mass at a chosen outcome. -/
noncomputable def dirac [DecidableEq A] (a : A) : ProbabilityVector A where
  prob x := if x = a then 1 else 0
  nonneg x := by positivity
  sum_eq_one := by simp

/-- The point mass is one at its chosen outcome and zero at every other outcome. -/
@[simp]
theorem dirac_apply [DecidableEq A] (a x : A) :
    dirac a x = if x = a then 1 else 0 :=
  rfl

/-- A binary probability vector `(t, 1-t)`. -/
noncomputable def binary (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ProbabilityVector (Fin 2) where
  prob i := if i = 0 then t else 1 - t
  nonneg i := by
    fin_cases i
    · simpa using ht.1
    · simpa using sub_nonneg.mpr ht.2
  sum_eq_one := by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp

/-- The first coordinate of the binary probability vector is its mass parameter. -/
@[simp]
theorem binary_zero (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : binary t ht 0 = t := by
  simp [binary]

/-- The second coordinate of the binary probability vector is one minus its mass parameter. -/
@[simp]
theorem binary_one (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : binary t ht 1 = 1 - t := by
  simp [binary]

/-- A binary probability vector on `Bool`, with mass `t` at `false`. -/
noncomputable def boolBinary (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ProbabilityVector Bool where
  prob b := if b then 1 - t else t
  nonneg b := by
    cases b
    · simpa using ht.1
    · simpa using sub_nonneg.mpr ht.2
  sum_eq_one := by
    rw [Fintype.sum_bool]
    simp

/-- The Boolean binary probability vector assigns its mass parameter to `false`. -/
@[simp]
theorem boolBinary_false (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    boolBinary t ht false = t := by
  simp [boolBinary]

/-- The Boolean binary probability vector assigns one minus its mass parameter to `true`. -/
@[simp]
theorem boolBinary_true (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    boolBinary t ht true = 1 - t := by
  simp [boolBinary]

/-- The binary probability vector varies continuously with its mass parameter. -/
theorem continuous_boolBinary :
    Continuous fun t : Set.Icc (0 : ℝ) 1 ↦ boolBinary t.1 t.2 := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  cases b
  · exact continuous_subtype_val
  · exact continuous_const.sub continuous_subtype_val

/-- The binary probability vector varies measurably with its mass parameter. -/
theorem measurable_boolBinary :
    Measurable fun t : Set.Icc (0 : ℝ) 1 ↦ boolBinary t.1 t.2 :=
  continuous_boolBinary.measurable

end ProbabilityVector

end FiniteMarkovKernels
