/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorUnrestrictedGamma.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorGreen
/-!
# Correspondence operator unrestricted gamma

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_integral_pointwiseGammaTwo_unrestricted`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
/-- The integrated pointwise iterated carré du champ equals the squared
actual differential generator on the paper's compact collision-free core. -/
theorem correspondenceOperator_integral_pointwiseGammaTwo_unrestricted {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ {z | CollisionFree z}) :
    (∫ z, ginibrePointwiseGammaTwo n f z ∂ginibreMeasure n) =
      ∫ z, (ginibrePregenerator n f z)^2 ∂ginibreMeasure n := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hs : tsupport f ⊆ {z | CollisionFree z} := hf.2.2
  let g := ginibrePregenerator n f
  have hg := correspondenceOperator_pregenerator_preserves_core hn f hf.1 hf.2.1 hs
  have hgg := correspondenceOperator_pregenerator_preserves_core hn g hg.1 hg.2.1 hg.2.2
  let Q : Configuration n → ℝ := fun z => (1/(n : ℝ))*∑ i : Fin n × Fin 2,
    (bochnerDirectionalDerivative (ginibreBochnerDirection i) f z)^2
  have hQ : ContDiff ℝ ∞ Q := by
    apply contDiff_const.mul
    apply ContDiff.sum
    intro i hi
    exact (bochnerDirectionalDerivative_contDiff _ f hf.1).pow 2
  have hcQ : HasCompactSupport Q := by
    apply HasCompactSupport.intro hf.2.1
    intro z hz
    simp [Q, bochnerDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hz]
  have hsQ : tsupport Q ⊆ {z | CollisionFree z} := by
    apply Set.Subset.trans _ hs
    apply closure_minimal _ (isClosed_tsupport f)
    intro z hz
    by_contra hh
    apply hz
    simp [Q, bochnerDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hh]
  have hAQ := correspondenceOperator_pregenerator_preserves_core hn Q hQ hcQ hsQ
  have hfg : ContDiff ℝ ∞ (fun z => f z*g z) := hf.1.mul hg.1
  have hcfg : HasCompactSupport (fun z => f z*g z) := hf.2.1.mul_right
  have hsfg : tsupport (fun z => f z*g z) ⊆ {z | CollisionFree z} :=
    tsupport_mul_subset_left.trans hs
  have hAfg := correspondenceOperator_pregenerator_preserves_core hn _ hfg hcfg hsfg
  have hiAQ : Integrable (ginibrePregenerator n Q) (ginibreMeasure n) :=
      hAQ.1.continuous.integrable_of_hasCompactSupport hAQ.2.1
  have hiAfg : Integrable (ginibrePregenerator n (fun z => f z*g z)) (ginibreMeasure n) :=
      hAfg.1.continuous.integrable_of_hasCompactSupport hAfg.2.1
  have hifgg : Integrable (fun z => f z*ginibrePregenerator n g z) (ginibreMeasure n) :=
    (hf.1.continuous.mul hgg.1.continuous).integrable_of_hasCompactSupport hf.2.1.mul_right
  have higg : Integrable (fun z => g z*g z) (ginibreMeasure n) :=
    (hg.1.continuous.mul hg.1.continuous).integrable_of_hasCompactSupport hg.2.1.mul_right
  have he : ginibrePointwiseGammaTwo n f =ᵐ[ginibreMeasure n]
      (fun z => ginibrePregenerator n Q z/2-
        (ginibrePregenerator n (fun y => f y*g y) z-f z*ginibrePregenerator n g z-g z*g z)/2) := by
    filter_upwards [ginibre_ae_collisionFree n hn] with z hz
    have hc := ginibrePointwiseGamma_eq_at hn f g z hz hf.1.contDiffAt hg.1.contDiffAt
    unfold ginibrePointwiseGamma at hc
    change (ginibrePregenerator n (fun y => f y*g y) z-f z*ginibrePregenerator n g z-g z*g
        z)/2=_ at hc
    change ginibrePregenerator n Q z/2-_=_
    rw [← hc]
  have hlinear := integral_sub (hiAQ.div_const 2) (((hiAfg.sub hifgg).sub higg).div_const 2)
  have hlinear2 := integral_sub (hiAfg.sub hifgg) higg
  have hlinear3 := integral_sub hiAfg hifgg
  simp only [Pi.sub_apply] at hlinear hlinear2 hlinear3
  rw [integral_congr_ae he, hlinear, integral_div, integral_div,
    hlinear2, hlinear3,
    correspondenceOperator_integral_pregenerator_eq_zero hn hQ hcQ,
    correspondenceOperator_integral_pregenerator_eq_zero hn hfg hcfg,
    correspondenceOperator_ginibre_mixed_green_identity hn hf hg.1]
  change 0/2-(0-(∫ z, g z*g z ∂ginibreMeasure n)-
    (∫ z, g z*g z ∂ginibreMeasure n))/2=∫ z, (g z)^2 ∂ginibreMeasure n
  simp only [pow_two]
  ring

end
end GinibrePoincare
