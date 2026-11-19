/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialGradientTransfer.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialEntropyTransfer
public import LeanPool.GinibrePoincare.Analysis.MagnitudeGradient

/-!
# Strong convex radial gradient transfer

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potential_magnitude_gradient_energy_eq_radiusProduct`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff NNReal
namespace GinibrePoincare
noncomputable section

theorem potential_coordinates_ne_zero_ae (n : ℕ) (V : Potential) :
    ∀ᵐ z ∂potentialMeasure n V, ∀ i, z i ≠ 0 := by
  have ha : potentialMeasure n V ≪ configurationVolume n :=
    (withDensity_absolutelyContinuous _ _).smul_left _
  apply ha.ae_le
  change ∀ᵐ z ∂(volume : Measure (Configuration n)), ∀ i, z i ≠ 0
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  change volume {z : Configuration n | ¬ z i ≠ 0} = 0
  rw [volume_pi]
  simpa only [Set.preimage, Set.mem_singleton_iff, not_not] using
    Measure.pi_eval_preimage_null (fun _ : Fin n => (volume : Measure ℂ))
      (i := i) (measure_singleton (0 : ℂ))

/-- The exact unweighted radial gradient identity holds under the actual nonquadratic gas. -/
theorem potential_realGradientNormSq_magnitude_ae (n : ℕ) (V : Potential)
    (F : (Fin n → ℝ) → ℝ) (hF : Differentiable ℝ F) :
    (fun z => realGradientNormSq (fun z => F (magnitudeVector z)) z) =ᵐ[potentialMeasure n V]
      (fun z => magnitudeEnergyDensity F (magnitudeVector z)) := by
  filter_upwards [potential_coordinates_ne_zero_ae n V] with z hz
  exact realGradientNormSq_magnitude F hF z hz

theorem magnitudeEnergyDensity_continuous_C1 {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ 1 F) : Continuous (magnitudeEnergyDensity F) := by
  unfold magnitudeEnergyDensity radiusPartial
  exact continuous_finsetSum _ fun i _ =>
    ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2

theorem magnitudeEnergyDensity_bound {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    {K : ℝ≥0} (hF : LipschitzWith K F) (r : Fin n → ℝ) :
    ‖magnitudeEnergyDensity F r‖ ≤ (n : ℝ) * (K : ℝ)^2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  unfold magnitudeEnergyDensity radiusPartial
  calc
    _ ≤ ∑ i : Fin n, (K : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
        simpa using congrArg (fun a : ℝ≥0 => (a : ℝ))
          (Pi.nnnorm_single (G := fun _ : Fin n => ℝ) (i := i) (1 : ℝ))
      have hb : ‖fderiv ℝ F r (Pi.single i 1)‖ ≤ (K : ℝ) := by
        calc
          _ ≤ ‖fderiv ℝ F r‖ * ‖(Pi.single i 1 : Fin n → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (K : ℝ) := by rw [hn, mul_one]; exact norm_fderiv_le_of_lipschitz ℝ hF
      rw [Real.norm_eq_abs] at hb
      nlinarith [sq_abs (fderiv ℝ F r (Pi.single i 1)), abs_nonneg (fderiv ℝ F r (Pi.single i 1))]
    _ = _ := by simp

theorem potential_magnitude_gradient_energy_eq_radiusProduct
    (n : ℕ) (hn : 0 < n) {V : Potential} (hVc : Continuous V)
    (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ 1 F)
    (hS : IsSymmetricRadiusTest n F) {K : ℝ≥0} (hLip : LipschitzWith K F) :
    potentialGradientEnergy n V (fun z => F (magnitudeVector z)) =
      ∫ r, directionalEnergy (fun i : Fin n => Pi.single i 1) F r ∂potentialRadiusProduct n V := by
  unfold potentialGradientEnergy
  rw [integral_congr_ae (potential_realGradientNormSq_magnitude_ae n V F
    (hF.differentiable (by simp)))]
  exact potential_magnitude_expectation_eq_radiusProduct n hn hVc hVr hfin
    (magnitudeEnergyDensity F) (magnitudeEnergyDensity_continuous_C1 F hF)
    (magnitudeEnergyDensity_symmetric F (hF.differentiable (by simp)) hS)
    ((n : ℝ) * (K : ℝ)^2) (magnitudeEnergyDensity_bound F hLip)

end
end GinibrePoincare
