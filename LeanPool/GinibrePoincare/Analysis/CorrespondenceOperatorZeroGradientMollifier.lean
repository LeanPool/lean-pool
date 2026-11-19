/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorZeroGradientMollifier.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorInvariantDensity
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorResolvent
public import LeanPool.GinibrePoincare.Analysis.GinibreDirectionalCoordinates
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.MeanValue
/-!
# Correspondence operator zero gradient mollifier

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_zero_gradient_mollification_fderiv`.
-/

@[expose] public section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
/-- Every directional distributional derivative of an actual unrestricted
zero-gradient weak pair vanishes. -/
theorem correspondenceOperator_zero_gradient_test {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (hu : IsGinibreDistributionalGradient n u 0)
    (v : Configuration n) (θ : Configuration n → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    (∫ z, u z*fderiv ℝ θ z v)=0 := by
  have hh := ginibre_distributional_gradient_directional n u 0 hu v θ hθ hc hs
  have he : (0 : GinibreFullGradientL2 n)=ᵐ[(volume : Measure (Configuration n))] fun _ => 0 :=
    (correspondenceOperator_volume_absolutelyContinuous_ginibre hn).ae_eq (Lp.coeFn_zero _ _ _)
  have hleft : (∫ z, (∑ k : Fin n×Fin 2, ginibreDirectionCoefficient v k*(0 : GinibreFullGradientL2
      n) z k)*θ z)=0 := by
    have hz : (fun z => (∑ k : Fin n×Fin 2, ginibreDirectionCoefficient v k*
        (0 : GinibreFullGradientL2 n) z k)*θ z)=ᵐ[volume] (fun _ => (0 : ℝ)) := by
      filter_upwards [he] with z hz
      rw [hz]
      simp
    rw [integral_congr_ae hz, integral_zero]
  rw [hleft] at hh
  exact neg_eq_zero.mp hh.symm

/-- A genuine compact cutoff of a zero-gradient observable has mollifications
with zero derivative wherever the translated smooth kernel remains inside the
cutoff's one-region in the collision-free domain. -/
theorem correspondenceOperator_zero_gradient_mollification_fderiv {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (hu : IsGinibreDistributionalGradient n u 0)
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ {z | CollisionFree z})
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (x : Configuration n)
    (hs : tsupport (fun y => φ (x - y)) ⊆ {z | CollisionFree z})
    (hηone : ∀ y ∈ tsupport (fun y => φ (x - y)), η y = 1) :
    fderiv ℝ ((fun y => u y*η y) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x=0 := by
  let θ : Configuration n→ℝ := fun y => φ (x-y)
  have hθ : ContDiff ℝ ∞ θ := hφ.comp (contDiff_const.sub contDiff_id)
  have hcθ : HasCompactSupport θ := hcφ.comp_homeomorph (Homeomorph.subLeft x)
  have hv : LocallyIntegrable (fun y => u y*η y) volume :=
    (integrable_mul_collisionFree_test _ η hu.1 hη.continuous hcη hsη).locallyIntegrable
  have hd := hcφ.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hv
    (hφ.of_le (by simp)) x
  rw [hd.fderiv]
  ext v
  rw [convolution_precompR_apply _ hv (hcφ.fderiv ℝ)
    (hφ.continuous_fderiv (by simp))]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, zero_apply]
  have hθd (y : Configuration n) : fderiv ℝ θ y v= -fderiv ℝ φ (x-y) v := by
    have hh := (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    simpa [θ, Function.comp_def] using
      congrArg (fun L : Configuration n→L[ℝ] ℝ => L v) hh.fderiv
  have hreplace : (fun y => u y*η y*fderiv ℝ φ (x-y) v)=
      fun y => -(u y*fderiv ℝ θ y v) := by
    funext y
    rw [hθd]
    by_cases hy : y∈tsupport θ
    · rw [hηone y hy]
      ring
    · have hh : fderiv ℝ θ y v=0 := by rw [fderiv_of_notMem_tsupport ℝ hy]; simp
      rw [hθd] at hh
      have hz := neg_eq_zero.mp hh
      simp [hz]
  rw [hreplace, integral_neg, correspondenceOperator_zero_gradient_test hn u hu v θ hθ hcθ hs,
      neg_zero]
end
end GinibrePoincare
