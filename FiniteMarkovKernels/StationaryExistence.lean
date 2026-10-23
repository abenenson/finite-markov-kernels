/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovKernels.BlockErgodicity
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Stationary laws on nonempty finite state spaces

Cesàro averages of any orbit lie in the compact finite probability simplex. A convergent
subsequence has a stationary limit, since shifting a bounded orbit changes its averages by a
quantity tending to zero. No irreducibility, positivity, or contraction assumption is needed.
-/

namespace FiniteMarkovKernels.FiniteMarkovKernel

open ProbabilityVector Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

private noncomputable def cesaro (kernel : FiniteMarkovKernel A A)
    (p : ProbabilityVector A) (n : ℕ) : ProbabilityVector A where
  prob a := ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), (kernel.apply^[k] p) a
  nonneg a := mul_nonneg (inv_nonneg.mpr (by positivity))
    (Finset.sum_nonneg fun k _hk ↦ (kernel.apply^[k] p).nonneg a)
  sum_eq_one := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [(kernel.apply^[ _ ] p).sum_eq_one, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by positivity)

private theorem cesaro_prob (kernel : FiniteMarkovKernel A A) (p : ProbabilityVector A)
    (n : ℕ) :
    (cesaro kernel p n).prob = birkhoffAverage ℝ kernel.apply ProbabilityVector.prob (n + 1) p := by
  funext a
  simp [cesaro, birkhoffAverage, birkhoffSum, Finset.sum_apply]

private theorem apply_cesaro_prob (kernel : FiniteMarkovKernel A A) (p : ProbabilityVector A)
    (n : ℕ) :
    (kernel.apply (cesaro kernel p n)).prob =
      birkhoffAverage ℝ kernel.apply ProbabilityVector.prob (n + 1) (kernel.apply p) := by
  classical
  funext a
  simp only [apply_prob, cesaro, birkhoffAverage, birkhoffSum, Pi.smul_apply,
    smul_eq_mul, Finset.sum_apply]
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  simp only [apply_prob]

/-- Every Markov kernel on a nonempty finite state space admits a stationary probability law. -/
theorem exists_isStationary [Nonempty A] (kernel : FiniteMarkovKernel A A) :
    ∃ law : ProbabilityVector A, kernel.IsStationary law := by
  classical
  let p := ProbabilityVector.dirac (Classical.arbitrary A)
  have hcube (n : ℕ) : (cesaro kernel p n).prob ∈ Set.Icc (0 : A → ℝ) 1 :=
    ⟨fun a ↦ (cesaro kernel p n).nonneg a,
      fun a ↦ (cesaro kernel p n).apply_le_one a⟩
  obtain ⟨r, hr, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hcube
  have hsum : ∑ a, r a = 1 := by
    have h := tendsto_finsetSum Finset.univ fun a _ha ↦ tendsto_pi_nhds.mp hlim a
    have hc : Tendsto (fun n ↦ ∑ a, (cesaro kernel p (φ n)) a) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sum_eq_one] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique h hc
  let law : ProbabilityVector A := ⟨r, hr.1, hsum⟩
  refine ⟨law, ProbabilityVector.ext fun a ↦ ?_⟩
  have hbound : Bornology.IsBounded (Set.range (ProbabilityVector.prob (A := A))) := by
    apply isCompact_Icc.isBounded.subset
    rintro _ ⟨q, rfl⟩
    exact ⟨q.nonneg, q.apply_le_one⟩
  have hshift := (tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ hbound
    kernel.apply p).comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
  have hzero : Tendsto
      (fun n ↦ (kernel.apply (cesaro kernel p (φ n))) a - (cesaro kernel p (φ n)) a)
      atTop (𝓝 0) := by
    have h := (_root_.continuous_apply a).tendsto (0 : A → ℝ)
    have hh := h.comp hshift
    change Tendsto (fun n ↦
      (birkhoffAverage ℝ kernel.apply ProbabilityVector.prob (φ n + 1) (kernel.apply p)) a -
      (birkhoffAverage ℝ kernel.apply ProbabilityVector.prob (φ n + 1) p) a)
      atTop (𝓝 0) at hh
    simp_rw [← apply_cesaro_prob] at hh
    simp_rw [← cesaro_prob] at hh
    exact hh
  have hmap : Tendsto (fun n ↦ (kernel.apply (cesaro kernel p (φ n))) a)
      atTop (𝓝 (kernel.apply law a)) := by
    simp only [apply_prob]
    exact tendsto_finsetSum Finset.univ fun b _hb ↦
      (tendsto_pi_nhds.mp hlim b).mul_const (kernel b a)
  have hdiff := hmap.sub (tendsto_pi_nhds.mp hlim a)
  exact sub_eq_zero.mp (tendsto_nhds_unique hdiff hzero)

/-- Strict contraction gives existence and uniqueness, without a supplied stationary law. -/
theorem existsUnique_isStationary_of_contractionCoefficient_lt_one [Nonempty A]
    (kernel : FiniteMarkovKernel A A) (hstrict : contractionCoefficient kernel < 1) :
    ∃! law : ProbabilityVector A, kernel.IsStationary law := by
  obtain ⟨law, hlaw⟩ := exists_isStationary kernel
  exact ⟨law, hlaw, fun q hq ↦
    eq_of_isStationary_of_contractionCoefficient_lt_one kernel hq hlaw hstrict⟩

/-- A strict finite block gives a unique stationary law for the original kernel. -/
theorem existsUnique_isStationary_of_iterate_contractionCoefficient_lt_one
    [Nonempty A] [DecidableEq A] (kernel : FiniteMarkovKernel A A) (block : ℕ)
    (hstrict : contractionCoefficient (iterate kernel block) < 1) :
    ∃! law : ProbabilityVector A, kernel.IsStationary law := by
  obtain ⟨law, hlaw⟩ := exists_isStationary kernel
  exact ⟨law, hlaw, fun q hq ↦
    eq_of_isStationary_of_iterate_contractionCoefficient_lt_one kernel block hq hlaw hstrict⟩

end FiniteMarkovKernels.FiniteMarkovKernel
