/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUERealMeasure.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEOrderedDensity
/-!
# Correspondence GUE real measure

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueOrderedMeasure_probability`, `gueOrderedMeasure_real_marginal_integral`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

theorem gueOrderedRawDensity_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0≤gueOrderedRawDensity n x := by
  unfold gueOrderedRawDensity gueOrderedPairWeight
  positivity

theorem gueOrderedRawDensity_integrable {n : ℕ} (hn : 0 < n) :
    Integrable (gueOrderedRawDensity n) volume := by
  have hs : Integrable (fun p : EuclideanSpace ℝ (Fin n)×EuclideanSpace ℝ (Fin n) =>
      gueOrderedRawDensity n p.1*gueAuxGaussianDensity n p.2) (volume.prod volume) := by
    apply ((gueSplit_volume_preserving n).integrable_comp_emb
      (gueSplitMeasurableEquiv n).measurableEmbedding).mp
    convert gueDoubledOrderedDensity_integrable hn using 1
    funext x
    simp only [Function.comp_apply, gueSplitMeasurableEquiv_apply]
    exact (gueDoubledOrderedDensity_split n x).symm
  obtain ⟨y, hy⟩ := hs.prod_left_ae.exists
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero (-(n : ℝ)/2*‖y‖^2)))
      (gueOrderedRawDensity n)).mp hy

theorem gueOrderedRawDensity_partition_pos {n : ℕ} (hn : 0 < n) :
    0<∫x, gueOrderedRawDensity n x := by
  exact lt_of_le_of_ne (integral_nonneg (gueOrderedRawDensity_nonneg n))
    (Ne.symm (gueOrderedRawDensity_partition_ne_zero hn))

/-- The ordered GUE measure: the density `gueOrderedRawDensity n` with respect to Lebesgue
measure, normalized by its total integral. -/
def gueOrderedMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (ENNReal.ofReal (∫x, gueOrderedRawDensity n x))⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (gueOrderedRawDensity n x))

theorem gueOrderedMeasure_probability {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (gueOrderedMeasure n) := by
  constructor
  unfold gueOrderedMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gueOrderedRawDensity_integrable hn)
      (Eventually.of_forall (gueOrderedRawDensity_nonneg n))]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (gueOrderedRawDensity_partition_pos hn)) ENNReal.ofReal_ne_top

theorem gueOrderedRawDensity_continuous (n : ℕ) : Continuous (gueOrderedRawDensity n) := by
  unfold gueOrderedRawDensity
  apply Continuous.mul
  · fun_prop
  · apply continuous_finsetProd
    intro p hp
    apply gueOrderedPairWeight_continuous.comp
    exact ((PiLp.proj 2 (fun _ : Fin n => ℝ) p.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous).sub
      ((PiLp.proj 2 (fun _ : Fin n => ℝ) p.1 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous)

theorem gueOrderedMeasure_integral (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫x, f x ∂gueOrderedMeasure n)=
      (∫x, gueOrderedRawDensity n x*f x)/(∫x, gueOrderedRawDensity n x) := by
  unfold gueOrderedMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul
    (μ := volume) (f := fun x => ENNReal.ofReal (gueOrderedRawDensity n x))
    ((gueOrderedRawDensity_continuous n).measurable.ennreal_ofReal)
    (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (gueOrderedRawDensity_nonneg n _),
      smul_eq_mul]
  rw [ENNReal.toReal_ofReal (integral_nonneg (gueOrderedRawDensity_nonneg n))]
  ring

theorem gueOrderedMeasure_real_marginal_integral {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫x, f (gueRealProjection n x) ∂gueDoubledOrderedMeasure n)=(∫x, f x ∂gueOrderedMeasure n) := by
  rw [gueOrderedMeasure_integral]
  exact gueDoubledOrderedMeasure_real_marginal_integral hn f

end
end GinibrePoincare
