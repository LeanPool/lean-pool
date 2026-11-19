/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BlockMagnitudeLift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BlockMagnitudeGradient
public import LeanPool.GinibrePoincare.Analysis.GaussianLSIReduction

/-!
# Block magnitude lift

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `compactSupport_block_magnitude_lift`, `lipschitz_block_magnitude_lift`,
`ginibre_magnitude_entropy_eq_block`, `ginibre_magnitude_energy_eq_block`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- The sharp Gaussian Lipschitz statement, proved by `gaussianBlock_lsi` for `n > 0`. -/
def GaussianBlockLipschitzLSIStatement (n : ℕ) : Prop :=
  ∀ H : GaussianRadialBlocks n → ℝ, (∃ K, LipschitzWith K H) → HasCompactSupport H →
    squareEntropy (gaussianRadialBlockMeasure n) H ≤
      (1 / (n : ℝ)) * ∫ x, blockGradientNormSq H x ∂gaussianRadialBlockMeasure n

private def blockEuclideanProjection (n : ℕ) (i : Fin n) :
    GaussianRadialBlocks n →L[ℝ] EuclideanSpace ℂ (Fin (i.val + 1)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (i.val + 1) => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj i)

theorem gaussianBlockMagnitude_eq_norm (k : ℕ) (x : Configuration k) :
    gaussianBlockMagnitude k x = ‖WithLp.toLp 2 x‖ := by
  have hs := PiLp.norm_sq_eq_of_L2 (fun _ : Fin k => ℂ) (WithLp.toLp 2 x)
  have he : configurationNormSq x = ‖WithLp.toLp 2 x‖ ^ 2 := by
    rw [hs]
    simp [configurationNormSq, Complex.normSq_eq_norm_sq]
  unfold gaussianBlockMagnitude
  rw [he, Real.sqrt_sq (norm_nonneg _)]

theorem lipschitz_blockMagnitudes (n : ℕ) : ∃ K, LipschitzWith K (blockMagnitudes n) := by
  let K : NNReal := Finset.univ.sup (fun i : Fin n => ‖blockEuclideanProjection n i‖₊)
  refine ⟨K, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ (K : ℝ) * dist x y)).mpr
  intro i
  change dist (gaussianBlockMagnitude _ (x i)) (gaussianBlockMagnitude _ (y i)) ≤ _
  rw [gaussianBlockMagnitude_eq_norm, gaussianBlockMagnitude_eq_norm]
  calc
    _ ≤ dist (blockEuclideanProjection n i x) (blockEuclideanProjection n i y) :=
      by
        simpa only [dist_eq_norm, blockEuclideanProjection, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
          ContinuousLinearMap.proj_apply] using
          dist_norm_norm_le (blockEuclideanProjection n i x) (blockEuclideanProjection n i y)
    _ ≤ (‖blockEuclideanProjection n i‖₊ : ℝ) * dist x y :=
      (blockEuclideanProjection n i).lipschitzWith.dist_le_mul x y
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.le_sup (s := Finset.univ)
        (f := fun i => ‖blockEuclideanProjection n i‖₊) (Finset.mem_univ i)))
      dist_nonneg

theorem compactSupport_block_magnitude_lift (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hc : HasCompactSupport F) : HasCompactSupport (fun x => F (blockMagnitudes n x)) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn continuous_id.continuousOn
  have hcompact : IsCompact ((blockMagnitudes n) ⁻¹' tsupport F) := by
    apply (isCompact_closedBall (0 : GaussianRadialBlocks n) (|C| + 1)).of_isClosed_subset
      ((isClosed_tsupport F).preimage (continuous_blockMagnitudes n))
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ |C| + 1)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ |C| + 1)).mpr
    intro j
    have hi : ‖x i j‖ ≤ blockMagnitudes n x i := by
      have hsq : ‖x i j‖ ^ 2 ≤ configurationNormSq (x i) := by
        rw [← Complex.normSq_eq_norm_sq]
        exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (x i k)) (Finset.mem_univ j)
      have hb := Real.sq_sqrt (configurationNormSq_nonneg (x i))
      have hbn := Real.sqrt_nonneg (configurationNormSq (x i))
      change ‖x i j‖ ≤ Real.sqrt (configurationNormSq (x i))
      nlinarith [norm_nonneg (x i j)]
    calc
      _ ≤ blockMagnitudes n x i := hi
      _ ≤ ‖blockMagnitudes n x i‖ := le_abs_self _
      _ ≤ ‖blockMagnitudes n x‖ := norm_le_pi_norm _ i
      _ ≤ C := hC _ hx
      _ ≤ |C| + 1 := by linarith [le_abs_self C]
  apply hcompact.of_isClosed_subset (isClosed_tsupport _)
  exact tsupport_comp_subset_preimage F (continuous_blockMagnitudes n)

theorem lipschitz_block_magnitude_lift (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∃ K, LipschitzWith K (fun x => F (blockMagnitudes n x)) := by
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hF (by simp)
  obtain ⟨B, hB⟩ := lipschitz_blockMagnitudes n
  exact ⟨A * B, hA.comp hB⟩

theorem ginibre_magnitude_entropy_eq_block (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hc : HasCompactSupport F)
    (hS : IsSymmetricRadiusTest n F) :
    squareEntropy (ginibreMeasure n) (fun z => F (magnitudeVector z)) =
      squareEntropy (gaussianRadialBlockMeasure n) (fun x => F (blockMagnitudes n x)) := by
  rw [ginibre_magnitude_entropy_eq_gamma n hn F hF hS hc,
    ← gaussianRadialBlockMeasure_map n hn]
  have he := squareEntropy_map (gaussianRadialBlockMeasure n) (gaussianBlockRadii n)
    ((contDiff_gaussianBlockRadii n).continuous.measurable.aemeasurable) (F ∘ gammaMagnitudes n)
    ((hF.comp (continuous_gammaMagnitudes n)).pow 2).aestronglyMeasurable
    (continuous_square_mul_log (hF.comp (continuous_gammaMagnitudes n))).aestronglyMeasurable
  change squareEntropy ((gaussianRadialBlockMeasure n).map (gaussianBlockRadii n))
    (fun r => F (gammaMagnitudes n r)) = _ at he
  simpa only [Function.comp_apply, gammaMagnitudes_blockRadii n hn] using he

theorem ginibre_magnitude_energy_eq_block (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hS : IsSymmetricRadiusTest n F) :
    smoothGinibreEnergy n (fun z => F (magnitudeVector z)) =
      (1 / (n : ℝ)) * ∫ x, blockGradientNormSq
        (fun x => F (blockMagnitudes n x)) x ∂gaussianRadialBlockMeasure n := by
  have hd := hF.differentiable (by simp)
  have hreal : (fun z => realGradientNormSq (fun z => F (magnitudeVector z)) z) =ᵐ[ginibreMeasure n]
      (fun z => magnitudeEnergyDensity F (magnitudeVector z)) := by
    filter_upwards [ginibre_coordinates_ne_zero_ae n hn] with z hz
    exact realGradientNormSq_magnitude F hd z hz
  have hblock : (fun x => blockGradientNormSq (fun x => F (blockMagnitudes n x)) x)
      =ᵐ[gaussianRadialBlockMeasure n]
      (fun x => magnitudeEnergyDensity F (blockMagnitudes n x)) := by
    filter_upwards [blockMagnitudes_pos_ae n hn] with x hx
    exact blockGradientNormSq_magnitude n hn F hd x hx
  obtain ⟨hcont, hcomp⟩ := magnitudeEnergyDensity_regular F hF hc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuous hcont
  have ht := ginibre_magnitude_expectation_eq_gamma n hn (magnitudeEnergyDensity F)
    hcont (magnitudeEnergyDensity_symmetric F hd hS) C hC
  unfold smoothGinibreEnergy
  rw [integral_congr_ae hreal, integral_congr_ae hblock, ht,
    ← gaussianRadialBlockMeasure_map n hn]
  congr 1
  have he := integral_map (μ := gaussianRadialBlockMeasure n) ((contDiff_gaussianBlockRadii
      n).continuous.measurable.aemeasurable)
    (hcont.comp (continuous_gammaMagnitudes n)).aestronglyMeasurable
  simpa only [Function.comp_apply, gammaMagnitudes_blockRadii n hn] using he

end
end GinibrePoincare
