/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianProjection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathFactorization
public import LeanPool.GinibrePoincare.Analysis.GaussianProjectionIndependence
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Orthogonal center and relative Brownian projections

`Configuration n` carries its usual function-space norm. To use Gaussian
orthogonality, `GinibreRealEuclidean n` equips the same coordinates with the
real Euclidean norm; `ginibreConfigToEuclidean` transports continuous linear
maps between these presentations.

The center projection is self-adjoint, and the recentering projection is its
complement. Their images are orthogonal because the center projection kills
a recentered configuration. These identities first show that each projected
noise is Brownian with the corresponding projected covariance, then imply
independence of the two entire processes by Gaussian orthogonality. -/

@[expose] public section

open scoped BigOperators ComplexConjugate NNReal
open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- The same finite configuration equipped with its standard real Euclidean norm. -/
abbrev GinibreRealEuclidean (n : ℕ) := PiLp 2 (fun _ : Fin n => ℂ)

/-- The projection onto the center-of-mass direction, replacing every coordinate by the mean
`(n : ℝ)⁻¹ • ∑ j, z j`. -/
def ginibreCenterProjectionCLM (n : ℕ) : Configuration n →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun _ => (n : ℝ)⁻¹ • coordinateSumCLM n

@[simp] theorem ginibreCenterProjectionCLM_apply (n : ℕ) (z : Configuration n) :
    ginibreCenterProjectionCLM n z = projectToCenterLine n z := by
  ext i
  simp [ginibreCenterProjectionCLM, projectToCenterLine, coordinateSumCLM_apply,
    div_eq_mul_inv, Complex.real_smul, mul_comm]

/-- The identification of `Configuration n` with the `L²` space `GinibreRealEuclidean n`. -/
def ginibreConfigToEuclidean (n : ℕ) : Configuration n ≃L[ℝ] GinibreRealEuclidean n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm

/-- The center-of-mass projection `ginibreCenterProjectionCLM n` transported to
`GinibreRealEuclidean n`. -/
def ginibreCenterProjectionEuclidean (n : ℕ) :
    GinibreRealEuclidean n →L[ℝ] GinibreRealEuclidean n :=
  (ginibreConfigToEuclidean n).toContinuousLinearMap.comp
    ((ginibreCenterProjectionCLM n).comp (ginibreConfigToEuclidean n).symm.toContinuousLinearMap)

/-- The recentering projection `recenteredCLM n` transported to `GinibreRealEuclidean n`. -/
def ginibreRecenterProjectionEuclidean (n : ℕ) :
    GinibreRealEuclidean n →L[ℝ] GinibreRealEuclidean n :=
  (ginibreConfigToEuclidean n).toContinuousLinearMap.comp
    ((recenteredCLM n).comp (ginibreConfigToEuclidean n).symm.toContinuousLinearMap)

@[simp] theorem ginibreConfigToEuclidean_apply (n : ℕ) (z : Configuration n) :
    ginibreConfigToEuclidean n z = WithLp.toLp 2 z := rfl

@[simp] theorem ginibreCenterProjectionEuclidean_apply (n : ℕ)
    (z : GinibreRealEuclidean n) :
    ginibreCenterProjectionEuclidean n z =
      WithLp.toLp 2 (projectToCenterLine n (WithLp.ofLp z)) := by
  simp [ginibreCenterProjectionEuclidean, ginibreConfigToEuclidean,
    PiLp.coe_continuousLinearEquiv, ginibreCenterProjectionCLM_apply]

@[simp] theorem ginibreRecenterProjectionEuclidean_apply (n : ℕ)
    (z : GinibreRealEuclidean n) :
    ginibreRecenterProjectionEuclidean n z =
      WithLp.toLp 2 (recenteredConfiguration n (WithLp.ofLp z)) := by
  simp [ginibreRecenterProjectionEuclidean, ginibreConfigToEuclidean,
    PiLp.coe_continuousLinearEquiv, recenteredCLM_apply]

theorem ginibreCenterProjectionEuclidean_selfAdjoint (n : ℕ)
    (x y : GinibreRealEuclidean n) :
    inner ℝ x (ginibreCenterProjectionEuclidean n y) =
      inner ℝ (ginibreCenterProjectionEuclidean n x) y := by
  simp only [ginibreCenterProjectionEuclidean_apply, PiLp.inner_apply, projectToCenterLine,
    coordinateSum, Complex.inner, Complex.mul_re, Complex.div_natCast_re, Complex.re_sum,
    Complex.conj_re, Complex.div_natCast_im, Complex.im_sum, Complex.conj_im, mul_neg,
    sub_neg_eq_add, map_div₀, map_sum, map_natCast, Finset.sum_neg_distrib,
    Finset.sum_sub_distrib]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem ginibreRecenterProjectionEuclidean_eq_sub (n : ℕ)
    (z : GinibreRealEuclidean n) :
    ginibreRecenterProjectionEuclidean n z =
      z - ginibreCenterProjectionEuclidean n z := by
  ext i
  simp [ginibreRecenterProjectionEuclidean_apply, ginibreCenterProjectionEuclidean_apply,
    recenteredConfiguration, projectToOrthogonal, projectToCenterLine]

theorem ginibreRecenterProjectionEuclidean_selfAdjoint (n : ℕ)
    (x y : GinibreRealEuclidean n) :
    inner ℝ x (ginibreRecenterProjectionEuclidean n y) =
      inner ℝ (ginibreRecenterProjectionEuclidean n x) y := by
  rw [ginibreRecenterProjectionEuclidean_eq_sub, ginibreRecenterProjectionEuclidean_eq_sub]
  simp only [inner_sub_right, inner_sub_left]
  rw [ginibreCenterProjectionEuclidean_selfAdjoint]

theorem ginibreCenterProjectionEuclidean_recenter_zero (n : ℕ)
    (z : GinibreRealEuclidean n) :
    ginibreCenterProjectionEuclidean n (ginibreRecenterProjectionEuclidean n z) = 0 := by
  rw [ginibreCenterProjectionEuclidean_apply, ginibreRecenterProjectionEuclidean_apply]
  have hs := coordinateSum_recentered n (WithLp.ofLp z)
  ext i
  simp [projectToCenterLine, hs]

theorem ginibreCenterRecenterEuclidean_orthogonal (n : ℕ)
    (x y : GinibreRealEuclidean n) :
    inner ℝ (ginibreCenterProjectionEuclidean n x)
      (ginibreRecenterProjectionEuclidean n y) = 0 := by
  rw [← ginibreCenterProjectionEuclidean_selfAdjoint n x
    (ginibreRecenterProjectionEuclidean n y)]
  rw [ginibreCenterProjectionEuclidean_recenter_zero n y]
  simp

/-- The actual Ginibre center and recentered projections preserve Brownian
paths and have the covariance of their respective orthogonal subspaces. -/
theorem ginibreBrownianNoise_projections_are_brownian
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → GinibreRealEuclidean n}
    (hB : IsBrownianVectorProcess B μ) :
    IsProjectedBrownianVectorProcess
      (fun t ω => ginibreCenterProjectionEuclidean n (B t ω)) μ
        (ginibreCenterProjectionEuclidean n) ∧
    IsProjectedBrownianVectorProcess
      (fun t ω => ginibreRecenterProjectionEuclidean n (B t ω)) μ
        (ginibreRecenterProjectionEuclidean n) := by
  exact ⟨hB.project _ (ginibreCenterProjectionEuclidean_selfAdjoint n),
    hB.project _ (ginibreRecenterProjectionEuclidean_selfAdjoint n)⟩

/-- A standard Gaussian configuration noise splits into independent center and
recentered noise processes. This is the Brownian-independence assertion in the
paper, stated in the finite-dimensional Gaussian-process formulation. -/
theorem ginibreGaussianNoise_center_recenter_independent
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → GinibreRealEuclidean n}
    (hB : IsBrownianVectorProcess B μ) :
    IndepFun (fun ω t => ginibreCenterProjectionEuclidean n (B t ω))
      (fun ω t => ginibreRecenterProjectionEuclidean n (B t ω)) μ := by
  apply orthogonalGaussianProjections_indepFun hB.toIsGaussianProcessWithBrownianCovariance
    (ginibreCenterProjectionEuclidean n) (ginibreRecenterProjectionEuclidean n)
  · exact ginibreCenterProjectionEuclidean_selfAdjoint n
  · exact ginibreRecenterProjectionEuclidean_selfAdjoint n
  · exact ginibreCenterRecenterEuclidean_orthogonal n

end
end GinibrePoincare
