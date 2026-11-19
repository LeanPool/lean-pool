/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare/GinibrePoincare/Concrete/Wirtinger.lean.
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

public import LeanPool.GinibrePoincare.Concrete.GaussianProbability

/-!
# Concrete Wirtinger derivatives and Gaussian holomorphic distance

The coordinate operators
`dbar_k = (∂_{x_k} + i ∂_{y_k}) / 2` are defined directly from the real
Fréchet derivative on `Configuration n`.
-/


@[expose] public section


open MeasureTheory
open scoped BigOperators ContDiff

namespace GinibrePoincare

noncomputable section

/-- A vector supported in one complex coordinate. -/
def coordinateDirection {n : ℕ} (k : Fin n) (w : ℂ) :
    Configuration n :=
  fun j => if j = k then w else 0

/-- Unit direction in the real part of coordinate `k`. -/
def realCoordinateDirection {n : ℕ} (k : Fin n) :
    Configuration n :=
  coordinateDirection k 1

/-- Unit direction in the imaginary part of coordinate `k`. -/
def imaginaryCoordinateDirection {n : ℕ} (k : Fin n) :
    Configuration n :=
  coordinateDirection k Complex.I

/-- Coordinate `dbar` derivative defined from the real Fréchet derivative. -/
def dbarComponent {n : ℕ} (g : Configuration n → ℂ)
    (k : Fin n) (z : Configuration n) : ℂ :=
  (1 / 2 : ℂ) *
    (fderiv ℝ g z (realCoordinateDirection k) +
      Complex.I * fderiv ℝ g z (imaginaryCoordinateDirection k))

/-- `dbarComponent` commutes with multiplication by a complex constant. -/
theorem dbarComponent_const_mul {n : ℕ} (a : ℂ)
    (f : Configuration n → ℂ) (hf : Differentiable ℝ f)
    (j : Fin n) (z : Configuration n) :
    dbarComponent (fun w => a * f w) j z = a * dbarComponent f j z := by
  unfold dbarComponent
  rw [fderiv_const_mul (hf z)]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- `dbarComponent` is additive over finite sums of differentiable functions. -/
theorem dbarComponent_finset_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → Configuration n → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (j : Fin n) (z : Configuration n) :
    dbarComponent (fun w => ∑ i ∈ s, f i w) j z =
      ∑ i ∈ s, dbarComponent (f i) j z := by
  unfold dbarComponent
  rw [fderiv_fun_sum (fun i hi => hf i hi z)]
  simp only [sum_apply]
  calc
    _ = (∑ i ∈ s, (1 / 2 : ℂ) *
          (fderiv ℝ (f i) z) (realCoordinateDirection j)) +
        ∑ i ∈ s, (1 / 2 : ℂ) * Complex.I *
          (fderiv ℝ (f i) z) (imaginaryCoordinateDirection j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      ring_nf
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Sum of the squared coordinate `dbar` derivatives at a point. -/
def dbarNormSq {n : ℕ} (g : Configuration n → ℂ)
    (z : Configuration n) : ℝ :=
  ∑ k : Fin n, Complex.normSq (dbarComponent g k z)

/-- Normalized Gaussian `dbar` energy. -/
def gaussianDbarEnergy (n : ℕ) (g : Configuration n → ℂ) : ℝ :=
  (1 / (n : ℝ)) *
    ∫ z, dbarNormSq g z ∂complexGaussianMeasure n

/-- Entire functions on the finite-dimensional complex configuration space. -/
def IsEntire {n : ℕ} (h : Configuration n → ℂ) : Prop :=
  Differentiable ℂ h

/-- Square-integrability of a complex function for the Gaussian measure. -/
def IsGaussianL2 (n : ℕ) (g : Configuration n → ℂ) : Prop :=
  Integrable (fun z => Complex.normSq (g z))
    (complexGaussianMeasure n)

/-- Form-domain conditions used by the representative-level `dbar` estimate. -/
def IsGaussianDbarAdmissible (n : ℕ)
    (g : Configuration n → ℂ) : Prop :=
  ContDiff ℝ ∞ g ∧ IsGaussianL2 n g ∧
    ∀ k : Fin n,
      Integrable (fun z => Complex.normSq (dbarComponent g k z))
        (complexGaussianMeasure n)

/-- Squared Gaussian `L²` error between two complex functions. -/
def gaussianComplexError (n : ℕ) (g h : Configuration n → ℂ) : ℝ :=
  ∫ z, Complex.normSq (g z - h z) ∂complexGaussianMeasure n

/-- Set of errors of entire square-integrable Gaussian approximants. -/
def gaussianHolomorphicErrors (n : ℕ)
    (g : Configuration n → ℂ) : Set ℝ :=
  {r | ∃ h : Configuration n → ℂ,
    IsEntire h ∧ IsGaussianL2 n h ∧
      r = gaussianComplexError n g h}

/-- Squared distance to the Gaussian holomorphic subspace, on representatives. -/
def gaussianHolomorphicDistanceSq (n : ℕ)
    (g : Configuration n → ℂ) : ℝ :=
  sInf (gaussianHolomorphicErrors n g)

/-- Exact target for the Gaussian `dbar` estimate. -/
def GaussianDbarEstimateStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ g : Configuration n → ℂ,
      IsGaussianDbarAdmissible n g →
      gaussianHolomorphicDistanceSq n g ≤ gaussianDbarEnergy n g

end

end GinibrePoincare
