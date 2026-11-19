/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianLSIReduction.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianRadialLift

/-!
# Gaussian LSI reduction

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `radial_lsi_of_gaussian_block_lsi`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- The smooth Gaussian block statement, discharged by `gaussian_smooth_lsi` for `n > 0`. -/
def GaussianBlockLSIStatement (n : ℕ) : Prop :=
  ∀ H : GaussianRadialBlocks n → ℝ, ContDiff ℝ ∞ H → HasCompactSupport H →
    squareEntropy (gaussianRadialBlockMeasure n) H ≤
      (1 / (n : ℝ)) * ∫ x, blockGradientNormSq H x ∂gaussianRadialBlockMeasure n

theorem contDiff_gaussianBlockRadii (n : ℕ) : ContDiff ℝ ∞ (gaussianBlockRadii n) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ ∞ (fun x : GaussianRadialBlocks n =>
    (n : ℝ) * ∑ j : Fin (i.val + 1), Complex.normSq (x i j))
  simp only [Complex.normSq_apply]
  change ContDiff ℝ ∞ (fun x : GaussianRadialBlocks n =>
    (n : ℝ) * ∑ j : Fin (i.val + 1),
      (Complex.reCLM (x i j) * Complex.reCLM (x i j) +
        Complex.imCLM (x i j) * Complex.imCLM (x i j)))
  apply contDiff_const.mul
  apply ContDiff.sum
  intro j hj
  have hp : ContDiff ℝ ∞ (fun x : GaussianRadialBlocks n => x i j) :=
    ((ContinuousLinearMap.proj j : Configuration (i.val + 1) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj i : GaussianRadialBlocks n →L[ℝ] Configuration (i.val +
          1))).contDiff
  have hr := Complex.reCLM.contDiff.comp hp
  have hi := Complex.imCLM.contDiff.comp hp
  exact (hr.mul hr).add (hi.mul hi)

/-- Compact profiles pull back to genuine compact Gaussian block tests. -/
theorem compactSupport_gaussian_radial_lift (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hc : HasCompactSupport F) :
    HasCompactSupport (fun x => F (gaussianBlockRadii n x)) := by
  have hq := (contDiff_gaussianBlockRadii n).continuous
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (continuous_id.continuousOn)
  have hcompact : IsCompact ((gaussianBlockRadii n) ⁻¹' tsupport F) := by
    apply (isCompact_closedBall (0 : GaussianRadialBlocks n) (|C| + 1)).of_isClosed_subset
      (isClosed_tsupport F |>.preimage hq)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ |C| + 1)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ |C| + 1)).mpr
    intro j
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbound : gaussianBlockRadius n (i.val + 1) (x i) ≤ C := by
      calc
        _ ≤ ‖gaussianBlockRadii n x i‖ := le_abs_self _
        _ ≤ ‖gaussianBlockRadii n x‖ := norm_le_pi_norm _ i
        _ ≤ C := hC _ hx
    have hs := configurationNormSq_nonneg (x i)
    have hj : Complex.normSq (x i j) ≤ configurationNormSq (x i) :=
      Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (x i k)) (Finset.mem_univ j)
    change (n : ℝ) * configurationNormSq (x i) ≤ C at hbound
    rw [Complex.normSq_eq_norm_sq] at hj
    have hnorm := norm_nonneg (x i j)
    have habs := le_abs_self C
    have habs0 := abs_nonneg C
    nlinarith [sq_nonneg (‖x i j‖ - (|C| + 1))]
  apply hcompact.of_isClosed_subset (isClosed_tsupport _)
  exact tsupport_comp_subset_preimage F hq

/-- Gaussian LSI implies the exact Ginibre radial inequality for every smooth
compact symmetric squared-radius profile. The Gaussian hypothesis is explicit. -/
theorem radial_lsi_of_gaussian_block_lsi (n : ℕ) (hn : 0 < n)
    (hG : GaussianBlockLSIStatement n)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hS : IsSymmetricRadiusTest n F) :
    ginibreSquareEntropy n (fun z => F (scaledSquaredRadii n z)) ≤
      smoothGinibreEnergy n (fun z => F (scaledSquaredRadii n z)) := by
  apply (radial_lsi_iff_gaussian_lift n hn F hF hc hS).mpr
  exact hG _ (hF.comp (contDiff_gaussianBlockRadii n))
    (compactSupport_gaussian_radial_lift n hn F hc)

end
end GinibrePoincare
