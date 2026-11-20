/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BakryEmeryNormalizedLift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BakryEmeryRegularizationVolume
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryHilbertLift
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsMass
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The Hilbert coordinate Haar factor cancels in the actual normalized Gibbs
law. Thus no unproved determinant normalization is needed for the block lift. -/

@[expose] public section
open MeasureTheory Measure Set Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual coordinate map from physical configurations to Hilbert blocks. -/
def bakryEmeryBlockHilbertEquiv (k : ℕ) :
    Configuration (k+1) ≃L[ℝ] BakryEmeryHilbertBlock k :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k+1) => ℂ)).symm

/-- Its image of physical volume is a positive, finite Haar multiple of
Hilbert volume; normalization cancels this actual factor. -/
theorem bakryEmeryBlockHilbert_volume (k : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧
      (volume : Measure (Configuration (k+1))).map (bakryEmeryBlockHilbertEquiv k) =
        c • (volume : Measure (BakryEmeryHilbertBlock k)) := by
  let e := bakryEmeryBlockHilbertEquiv k
  let μ := (volume : Measure (Configuration (k+1))).map e
  let : IsAddHaarMeasure μ := e.isAddHaarMeasure_map volume
  refine ⟨addHaarScalarFactor μ volume, addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume,?_⟩
  exact isAddLeftInvariant_eq_smul μ volume

/-- Every literal normalized Gibbs expectation agrees in the two coordinate
representations; the Haar coefficient is proved and cancels algebraically. -/
theorem bakryEmeryBlockHilbert_normalized_integral (k : ℕ)
    (W : BakryEmeryHilbertBlock k → ℝ) (hW : Continuous W)
    (f : BakryEmeryHilbertBlock k → ℝ) :
    (∫ z, f (bakryEmeryBlockHilbertEquiv k z) ∂bakryEmeryNormalizedGibbs volume
      (fun z => W (bakryEmeryBlockHilbertEquiv k z))) =
      ∫ x, f x ∂bakryEmeryNormalizedGibbs volume W := by
  let e := bakryEmeryBlockHilbertEquiv k
  obtain ⟨c, hc, he⟩ := bakryEmeryBlockHilbert_volume k
  have hInt (q : BakryEmeryHilbertBlock k → ℝ) :
      (∫ z : Configuration (k+1), q (e z)) = (c : ℝ) * ∫ x, q x := by
    have h := integral_map_equiv (μ := (volume : Measure (Configuration (k+1))))
      e.toHomeomorph.toMeasurableEquiv q
    change (∫ x, q x ∂(volume : Measure (Configuration (k+1))).map e) = _ at h
    rw [he, integral_smul_nnreal_measure] at h
    simpa [NNReal.smul_def, smul_eq_mul] using h.symm
  have hcomp : Continuous (fun z => W (e z)) := hW.comp e.continuous
  change (∫ z, f (e z) ∂bakryEmeryNormalizedGibbs volume (fun z => W (e z))) = _
  rw [bakryEmeryNormalizedGibbs_integral (volume : Measure (Configuration (k+1)))
    (fun z => W (e z)) hcomp (fun z => f (e z)),
    bakryEmeryNormalizedGibbs_integral (volume : Measure (BakryEmeryHilbertBlock k)) W hW f]
  change (∫ z, (Real.exp (-W (e z))*f (e z))) / (∫ z, Real.exp (-W (e z))) = _
  rw [hInt (fun x => Real.exp (-W x)*f x), hInt (fun x => Real.exp (-W x))]
  exact mul_div_mul_left _ _ (by exact_mod_cast hc.ne' : (c : ℝ) ≠ 0)

/-- Actual square entropy agrees between physical and Hilbert coordinates. -/
theorem bakryEmeryBlockHilbert_normalized_entropy (k : ℕ)
    (W : BakryEmeryHilbertBlock k → ℝ) (hW : Continuous W)
    (f : BakryEmeryHilbertBlock k → ℝ) :
    squareEntropy (bakryEmeryNormalizedGibbs volume
      (fun z => W (bakryEmeryBlockHilbertEquiv k z)))
      (fun z => f (bakryEmeryBlockHilbertEquiv k z)) =
        squareEntropy (bakryEmeryNormalizedGibbs volume W) f := by
  unfold squareEntropy
  rw [bakryEmeryBlockHilbert_normalized_integral k W hW (fun x => f x^2*Real.log (f x^2)),
    bakryEmeryBlockHilbert_normalized_integral k W hW (fun x => f x^2)]

/-- The literal normalized block law is exactly the normalized Gibbs law
of the proved Hilbert confinement pulled back to physical coordinates. -/
theorem bakryEmeryBlockLift_eq_normalizedGibbs
    (n k : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    bakryEmeryBlockLift n k V = bakryEmeryNormalizedGibbs volume
      (fun z => bakryEmeryEuclideanLiftPotential n V (bakryEmeryBlockHilbertEquiv k z)) := by
  let e := bakryEmeryBlockHilbertEquiv k
  let W : BakryEmeryHilbertBlock k → ℝ := bakryEmeryEuclideanLiftPotential n V
  have hI : Integrable (fun x => Real.exp (-W x)) volume := by
    simpa [W, bakryEmeryRegularizedLiftPotential, bakryEmeryEuclideanLiftPotential,
      Real.sqrt_sq (norm_nonneg _)] using
      bakryEmeryRegularizedLift_density_integrable (E := BakryEmeryHilbertBlock k)
        n hn ρ hρ V hV hrot hc 0
  obtain ⟨c, hc', he⟩ := bakryEmeryBlockHilbert_volume k
  have hIm : Integrable (fun x => Real.exp (-W x))
      ((volume : Measure (Configuration (k+1))).map e) := by
    rw [he]
    exact hI.smul_measure_nnreal
  have hIs := (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv
    (fun x => Real.exp (-W x))).mp hIm
  change Integrable (fun z => Real.exp (-W (e z))) volume at hIs
  have hraw : bakryEmeryRawBlockLift n k V =
      volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-W (e z)))) := by
    unfold bakryEmeryRawBlockLift
    congr 1
    funext z
    have hp := bakryEmeryBlock_profile_eq_hilbert_potential n k V z
    change (n : ℝ)*potentialSquaredRadiusProfile V (gaussianBlockRadius 1 (k+1) z) = W (e z) at hp
    rw [neg_mul, hp]
  have hm : bakryEmeryRawBlockLift n k V univ =
      ENNReal.ofReal (∫ z, Real.exp (-W (e z))) := by
    rw [hraw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hIs
        (Eventually.of_forall (fun z => Real.exp_nonneg _))]
  unfold bakryEmeryBlockLift bakryEmeryNormalizedGibbs
  rw [hm, hraw]

/-- The literal radial block entropy equals the normalized Hilbert Gibbs
entropy, with all normalization and confinement integrability proved internally. -/
theorem bakryEmeryBlockLift_hilbert_entropy
    (n k : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : BakryEmeryHilbertBlock k → ℝ) :
    squareEntropy (bakryEmeryBlockLift n k V)
      (fun z => f (bakryEmeryBlockHilbertEquiv k z)) =
      squareEntropy (bakryEmeryNormalizedGibbs volume (bakryEmeryEuclideanLiftPotential n V)) f :=
          by
  rw [bakryEmeryBlockLift_eq_normalizedGibbs n k hn ρ hρ V hV hrot hc]
  exact bakryEmeryBlockHilbert_normalized_entropy k _
    (continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp continuous_norm))) f

end
end GinibrePoincare
