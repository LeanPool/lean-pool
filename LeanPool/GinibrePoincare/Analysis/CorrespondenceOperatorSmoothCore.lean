/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorSmoothCore.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseBochner
public import LeanPool.GinibrePoincare.Analysis.GinibreGeneratorL2
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoffEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff

/-!
# Correspondence operator smooth core

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_integral_pointwiseGammaTwo`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The actual differential generator preserves smoothness for compact tests
whose support avoids collisions. No symmetry hypothesis is required. -/
theorem correspondenceOperator_pregenerator_contDiff {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ {z | CollisionFree z}) :
    ContDiff ℝ ∞ (ginibrePregenerator n f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · exact ginibrePregenerator_contDiffAt_of_contDiff hn f hf z (hs hz)
  · have he : ginibrePregenerator n f =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hz] with y hy
      exact ginibrePregenerator_eq_zero_of_notMem_tsupport f hy
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const he

/-- Locality keeps the generator support inside the original test support. -/
theorem correspondenceOperator_pregenerator_tsupport {n : ℕ}
    (f : Configuration n → ℝ) :
    tsupport (ginibrePregenerator n f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro z hz
  by_contra h
  exact hz (ginibrePregenerator_eq_zero_of_notMem_tsupport f h)

/-- The unrestricted smooth collision-free compact core is preserved by the
concrete differential generator. -/
theorem correspondenceOperator_pregenerator_preserves_core {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {z | CollisionFree z}) :
    ContDiff ℝ ∞ (ginibrePregenerator n f) ∧
    HasCompactSupport (ginibrePregenerator n f) ∧
    tsupport (ginibrePregenerator n f) ⊆ {z | CollisionFree z} :=
  ⟨correspondenceOperator_pregenerator_contDiff hn f hf hs,
    hasCompactSupport_ginibrePregenerator hc,
    (correspondenceOperator_pregenerator_tsupport f).trans hs⟩

/-- Invariance on every smooth compact test, without permutation symmetry. -/
theorem correspondenceOperator_integral_pregenerator_eq_zero {n : ℕ} (hn : 0 < n)
    {f : Configuration n → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∫ z, ginibrePregenerator n f z ∂ginibreMeasure n = 0  := by
  have hSmooth (v : Configuration n) : ContDiff ℝ ∞
      (fun z => ginibreLebesgueDensityReal n z * fderiv ℝ f z v) :=
    (contDiff_ginibreLebesgueDensityReal n).mul
      ((hf.contDiff_fderiv_apply (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const))
  have hCompact (v : Configuration n) : HasCompactSupport
      (fun z => ginibreLebesgueDensityReal n z * fderiv ℝ f z v) :=
    (hc.fderiv_apply ℝ v).mul_left
  have hInt (v : Configuration n) : Integrable (fun z => fderiv ℝ
      (fun y => ginibreLebesgueDensityReal n y * fderiv ℝ f y v) z v) volume :=
    (((hSmooth v).continuous_fderiv (by simp)).clm_apply
        continuous_const).integrable_of_hasCompactSupport ((hCompact v).fderiv_apply ℝ v)
  rw [integral_ginibreMeasure_eq_density_volume hn]
  have hcf : ∀ᵐ z ∂(configurationVolume n), CollisionFree z := by
    rw [ae_iff]
    have heq : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z
      rw [Set.mem_ofPred_eq, collisionFree_iff_not_mem_collisionSet]
      simp
    rw [heq]
    exact configurationVolume_collisionSet hn
  have hdiv : (∫ z, ginibreLebesgueDensityReal n z *
      ginibrePregenerator n f z) =
      ∫ z, (1 / (n : ℝ)) * ∑ j : Fin n,
        (fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (realCoordinateDirection j)) z
              (realCoordinateDirection j) +
          fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
            fderiv ℝ f y (imaginaryCoordinateDirection j)) z
              (imaginaryCoordinateDirection j)) := by
    apply integral_congr_ae
    filter_upwards [hcf] with z hz
    exact ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence
      hn f hf z hz
  rw [hdiv, integral_const_mul, integral_finsetSum]
  · simp_rw [integral_add
        (hInt _)
        (hInt _)]
    have hzR (j : Fin n) :
        (∫ z, fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
          fderiv ℝ f y (realCoordinateDirection j)) z
            (realCoordinateDirection j)) = 0 :=
      integral_fderiv_configuration_real_eq_zero _
        ((hSmooth _).of_le (by simp))
        (hCompact _) j
    have hzI (j : Fin n) :
        (∫ z, fderiv ℝ (fun y => ginibreLebesgueDensityReal n y *
          fderiv ℝ f y (imaginaryCoordinateDirection j)) z
            (imaginaryCoordinateDirection j)) = 0 :=
      integral_fderiv_configuration_imag_eq_zero _
        ((hSmooth _).of_le (by simp))
        (hCompact _) j
    simp [hzR, hzI]
  · intro j hj
    exact (hInt _).add
      (hInt _)

/-- The integrated pointwise iterated carré du champ equals the squared generator for every
smooth compactly supported collision-free test `f`, given the mixed Green identity for the
pair `(f, Lf)`. -/
theorem correspondenceOperator_integral_pointwiseGammaTwo_of_green {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ {z | CollisionFree z})
    (hgreen : (∫ z, f z * ginibrePregenerator n (ginibrePregenerator n f) z ∂ginibreMeasure n) =
      ∫ z, ginibrePregenerator n f z * ginibrePregenerator n f z ∂ginibreMeasure n) :
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
    hgreen]
  change 0/2-(0-(∫ z, g z*g z ∂ginibreMeasure n)-
    (∫ z, g z*g z ∂ginibreMeasure n))/2=∫ z, (g z)^2 ∂ginibreMeasure n
  simp only [pow_two]
  ring

/-- The integrated pointwise iterated carré du champ equals the squared
actual differential generator on the paper's compact collision-free core. -/
theorem correspondenceOperator_integral_pointwiseGammaTwo {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (∫ z, ginibrePointwiseGammaTwo n f z ∂ginibreMeasure n) =
      ∫ z, (ginibrePregenerator n f z)^2 ∂ginibreMeasure n := by
  have hs : tsupport f ⊆ {z | CollisionFree z} := fun z hz =>
    (collisionFree_iff_not_mem_collisionSet z).mpr (hf.2.2.1 hz)
  exact correspondenceOperator_integral_pointwiseGammaTwo_of_green hn f ⟨hf.1, hf.2.1, hs⟩
    (ginibre_mixed_green_identity hn hf
      (correspondenceOperator_pregenerator_preserves_core hn f hf.1 hf.2.1 hs).1)

end
end GinibrePoincare
