/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialMollifierKernels.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialConvolutionInvariance

/-! # Concrete normalized shrinking radial mollifier kernels

These kernels use the smooth cutoff of the total squared radius, preserving
all independent coordinate phases and all particle permutations.
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution BigOperators
namespace GinibrePoincare
noncomputable section

/-- The smooth compactly supported radial bump `ginibreSpatialCutoff n 0` evaluated at the
rescaled point `(m + 1) • z`. -/
def radialMollifierBase (n m : ℕ) (z : Configuration n) : ℝ :=
  ginibreSpatialCutoff n 0 (((m : ℝ) + 1) • z)

theorem radialMollifierBase_smooth (n m : ℕ) : ContDiff ℝ ∞ (radialMollifierBase n m) := by
  unfold radialMollifierBase
  apply (ginibreSpatialCutoff_smooth n 0).comp
  fun_prop

theorem radialMollifierBase_compact (n m : ℕ) : HasCompactSupport (radialMollifierBase n m) :=
  (ginibreSpatialCutoff_compact n 0).comp_isClosedEmbedding
    (Homeomorph.smulOfNeZero ((m : ℝ) + 1) (by positivity)).isClosedEmbedding

theorem radialMollifierBase_nonneg (n m : ℕ) (z : Configuration n) :
    0 ≤ radialMollifierBase n m z := (ginibreSpatialCutoff_mem_unit n 0 _).1

theorem radialMollifierBase_integrable (n m : ℕ) : Integrable (radialMollifierBase n m) :=
  (radialMollifierBase_smooth n m).continuous.integrable_of_hasCompactSupport
    (radialMollifierBase_compact n m)

theorem radialMollifierBase_mass_pos (n m : ℕ) : 0 < ∫ z, radialMollifierBase n m z := by
  apply integral_pos_of_integrable_nonneg_ne_zero (x := 0)
    (radialMollifierBase_smooth n m).continuous (radialMollifierBase_integrable n m)
    (radialMollifierBase_nonneg n m)
  have hb : sobolevCutoffBump (0 : ℝ) = 1 := sobolevCutoffBump.one_of_mem_closedBall (by
    simp [sobolevCutoffBump])
  simp [radialMollifierBase, ginibreSpatialCutoff, sobolevCutoff, configurationNormSq, hb]

/-- The radial bump `radialMollifierBase n m` normalized to have total Lebesgue integral one. -/
def radialMollifierKernel (n m : ℕ) (z : Configuration n) : ℝ :=
  (∫ y, radialMollifierBase n m y)⁻¹ * radialMollifierBase n m z

/-- The concrete kernel is nonnegative, smooth, compact and normalized. -/
theorem radialMollifierKernel_properties (n m : ℕ) :
    ContDiff ℝ ∞ (radialMollifierKernel n m) ∧
      HasCompactSupport (radialMollifierKernel n m) ∧
      (∀ z, 0 ≤ radialMollifierKernel n m z) ∧
      Integrable (radialMollifierKernel n m) ∧
      (∫ z, radialMollifierKernel n m z) = 1 := by
  have hp := radialMollifierBase_mass_pos n m
  refine ⟨contDiff_const.mul (radialMollifierBase_smooth n m),
    (radialMollifierBase_compact n m).mul_left, ?_,
    (radialMollifierBase_integrable n m).const_mul _, ?_⟩
  · intro z
    exact mul_nonneg (inv_nonneg.mpr hp.le) (radialMollifierBase_nonneg n m z)
  · unfold radialMollifierKernel
    rw [integral_const_mul, inv_mul_cancel₀ hp.ne']

/-- These actual kernels depend only on individual squared radii. -/
theorem radialMollifierKernel_radial (n m : ℕ) :
    ∃ F : (Fin n → ℝ) → ℝ, ∀ z,
      radialMollifierKernel n m z = F (fun i => Complex.normSq (z i)) := by
  apply radial_of_coordinatePhase
  intro u hu z
  unfold radialMollifierKernel radialMollifierBase
  congr 1
  have he : ((m : ℝ) + 1) • coordinatePhase u z =
      coordinatePhase u (((m : ℝ) + 1) • z) := by
    ext i
    simp [coordinatePhase, Complex.real_smul, mul_left_comm]
  rw [he]
  exact radial_coordinatePhase (ginibreSpatialCutoff_radial n 0) u hu _

/-- The actual kernels are symmetric under particle relabelling. -/
theorem radialMollifierKernel_symmetric (n m : ℕ) : IsSymmetric (radialMollifierKernel n m) := by
  intro σ z
  unfold radialMollifierKernel radialMollifierBase
  congr 1
  exact ginibreSpatialCutoff_symmetric n 0 σ (((m : ℝ) + 1) • z)

/-- Support of the normalized kernels shrinks to zero with an explicit bound. -/
theorem radialMollifierKernel_support_bound (n m : ℕ) (z : Configuration n)
    (hz : z ∈ Function.support (radialMollifierKernel n m)) :
    ‖z‖ ≤ 2 / ((m : ℝ) + 1) := by
  have hb : radialMollifierBase n m z ≠ 0 := by
    intro he
    exact hz (by simp [radialMollifierKernel, he])
  have ht : ((m : ℝ) + 1) • z ∈ tsupport (ginibreSpatialCutoff n 0) :=
    subset_tsupport _ hb
  have hS := ginibreSpatialCutoff_support_bound n 0 ht
  simp only [Set.mem_ofPred_eq, Nat.cast_zero, zero_add, mul_one] at hS
  have hn : 0 < (m : ℝ) + 1 := by positivity
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hi : Complex.normSq ((((m : ℝ) + 1) • z) i) ≤
      configurationNormSq (((m : ℝ) + 1) • z) :=
    Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hnorm : Complex.normSq ((((m : ℝ) + 1) • z) i) =
      (((m : ℝ) + 1) * ‖z i‖) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hn]
  rw [hnorm] at hi
  apply (le_div_iff₀ hn).mpr
  nlinarith [norm_nonneg (z i)]

/-- Convolution by the actual normalized kernels lies in the original radial core. -/
theorem radialMollifierKernel_convolution_core (n m : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    IsRadialSobolevCore (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) := by
  obtain ⟨hk, hkc, _⟩ := radialMollifierKernel_properties n m
  exact ⟨⟨hkc.contDiff_convolution_left _ hk (hf.locallyIntegrable (by norm_num)),
    hkc.convolution _ hc,
    symmetric_convolution _ _ (radialMollifierKernel_symmetric n m) hs⟩,
    radial_convolution _ _ (radialMollifierKernel_radial n m) hr⟩

end
end GinibrePoincare
