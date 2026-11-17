/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreMassPositivity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianDensity
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Strict positivity of the Ginibre normalizing mass -/


@[expose] public section


open MeasureTheory
open scoped ENNReal BigOperators

namespace GinibrePoincare

noncomputable section

/-- The Vandermonde polynomial is continuous on configuration space. -/
theorem continuous_vandermonde {n : ℕ} :
    Continuous (vandermonde : Configuration n → ℂ) := by
  rw [show (vandermonde : Configuration n → ℂ) =
      fun z ↦ ∏ i : Fin n, ∏ j > i, (z j - z i) by
    funext z
    exact vandermonde_eq_product z]
  fun_prop

/-- The extended nonnegative Vandermonde density is measurable. -/
theorem measurable_vandermondeDensity {n : ℕ} :
    Measurable (vandermondeDensity : Configuration n → ℝ≥0∞) := by
  unfold vandermondeDensity vandermondeWeight
  exact ENNReal.measurable_ofReal.comp
    (Complex.continuous_normSq.comp continuous_vandermonde).measurable

/-- The explicit complex Gaussian density is measurable. -/
theorem measurable_complexGaussianDensity (n : ℕ) :
    Measurable (complexGaussianDensity n) := by
  unfold complexGaussianDensity gaussianWeight configurationNormSq
  fun_prop

/-- At positive particle number the explicit Gaussian density is everywhere
strictly positive. -/
theorem complexGaussianDensity_pos {n : ℕ} (hn : 0 < n)
    (z : Configuration n) : 0 < complexGaussianDensity n z := by
  unfold complexGaussianDensity
  rw [ENNReal.ofReal_pos]
  exact mul_pos
    (pow_pos (div_pos (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
      Real.pi_pos) n)
    (gaussianWeight_pos n z)

/-- Every nonempty open subset of configuration space has positive Gaussian
measure. -/
theorem complexGaussianMeasure_isOpenPosMeasure {n : ℕ} (hn : 0 < n)
    {U : Set (Configuration n)} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < complexGaussianMeasure n U := by
  rw [complexGaussianDensityIdentification n hn,
    complexGaussianDensityMeasure, configurationVolume,
    withDensity_apply _ hU.measurableSet]
  rw [setLIntegral_pos_iff (measurable_complexGaussianDensity n)]
  have hsupp : Function.support (complexGaussianDensity n) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (complexGaussianDensity_pos hn z).ne'
  rw [hsupp, Set.univ_inter]
  exact hU.measure_pos (volume : Measure (Configuration n)) hne

/-- A canonical collision-free configuration, obtained by placing the
particles at distinct nonnegative integers on the real axis. -/
def integerConfiguration (n : ℕ) : Configuration n :=
  fun i ↦ (i.val : ℂ)

theorem integerConfiguration_collisionFree (n : ℕ) :
    CollisionFree (integerConfiguration n) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Complex.re hij
  simp only [integerConfiguration, Complex.natCast_re, Nat.cast_inj] at h
  exact_mod_cast h

/-- The set on which the Vandermonde density is nonzero is open and nonempty. -/
theorem support_vandermondeDensity_isOpen_nonempty (n : ℕ) :
    IsOpen (Function.support
      (vandermondeDensity : Configuration n → ℝ≥0∞)) ∧
    (Function.support
      (vandermondeDensity : Configuration n → ℝ≥0∞)).Nonempty := by
  constructor
  · have hcont : Continuous
        (fun z : Configuration n ↦ Complex.normSq (vandermonde z)) :=
      Complex.continuous_normSq.comp continuous_vandermonde
    have hopen : IsOpen
        {z : Configuration n | Complex.normSq (vandermonde z) ≠ 0} :=
      isClosed_singleton.isOpen_compl.preimage hcont
    simpa [Function.support, vandermondeDensity, vandermondeWeight,
      ENNReal.ofReal_eq_zero, Complex.normSq_nonneg] using hopen
  · refine ⟨integerConfiguration n, ?_⟩
    simp only [Function.mem_support, vandermondeDensity, vandermondeWeight]
    exact (ENNReal.ofReal_pos.mpr (Complex.normSq_pos.mpr
      ((vandermonde_ne_zero_iff _).mpr
        (integerConfiguration_collisionFree n)))).ne'

/-- The raw Ginibre normalizing mass is strictly positive.  This result is
independent of its finiteness. -/
theorem ginibreNormalizingMass_pos {n : ℕ} (hn : 0 < n) :
    0 < ginibreNormalizingMass n := by
  unfold ginibreNormalizingMass rawGinibreMeasure
  rw [withDensity_apply' _ Set.univ]
  rw [Measure.restrict_univ]
  rw [lintegral_pos_iff_support measurable_vandermondeDensity]
  rcases support_vandermondeDensity_isOpen_nonempty n with ⟨hopen, hne⟩
  exact complexGaussianMeasure_isOpenPosMeasure hn hopen hne

end

end GinibrePoincare
