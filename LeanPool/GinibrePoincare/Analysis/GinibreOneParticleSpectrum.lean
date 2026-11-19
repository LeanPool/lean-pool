/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreOneParticleSpectrum.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCenterEigenvectors
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSmoothIdentification
public import LeanPool.GinibrePoincare.Analysis.SumRadiusCoordinates

/-! # Corollary 1.5 including the one-particle case

Holomorphic powers of the Gaussian center have actual square-integrable
ordinary gradients, belong to the full weak generator domain, and have
eigenvalues `-2k`. This construction works for every positive particle count,
independently of the Hermite–Laguerre radius sector (which assumes `n ≥ 2`).
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

private theorem coordinateSum_differentiable (n : ℕ) :
    Differentiable ℝ (coordinateSum : Configuration n → ℂ) := by
  have he : (coordinateSum : Configuration n → ℂ) = coordinateSumCLM n := by
    funext z; simp
  rw [he]
  exact (coordinateSumCLM n).differentiable

theorem coordinateSum_power_memLp (n : ℕ) (hn : 0 < n) (k : ℕ) :
    MemLp (fun z : Configuration n => coordinateSum z ^ k) 2 (ginibreMeasure n) := by
  have hm : MemLp (fun s : ℂ => s ^ k) 2 standardComplexGaussianMeasure := by
    apply (memLp_two_iff_integrable_sq_norm (continuous_id.pow k).aestronglyMeasurable).mpr
    simpa [norm_pow, ← pow_mul, standardComplexGaussianMeasure] using
      integrable_norm_pow_complexCoordinateGaussianProbability 1 (k * 2)
  exact hm.comp_measurePreserving
    ⟨measurable_coordinateSum n, coordinateSum_ginibre_gaussian n hn⟩

theorem fderiv_coordinateSum_power (n k : ℕ) (z v : Configuration n) :
    fderiv ℝ (fun w : Configuration n => coordinateSum w ^ k) z v =
      (k : ℂ) * coordinateSum z ^ (k - 1) * coordinateSum v := by
  change (fderiv ℝ ((coordinateSum : Configuration n → ℂ) ^ k) z) v = _
  rw [fderiv_pow k (coordinateSum_differentiable n z)]
  simp [fderiv_coordinateSum, smul_eq_mul]

theorem coordinateSum_power_second (n k : ℕ) (z v : Configuration n) :
    complexSecondDirectionalDerivative (fun w : Configuration n => coordinateSum w ^ k) v z =
      (k : ℂ) * ((k - 1 : ℕ) : ℂ) * coordinateSum z ^ (k - 1 - 1) *
        coordinateSum v ^ 2 := by
  unfold complexSecondDirectionalDerivative
  simp_rw [fderiv_coordinateSum_power]
  rw [fderiv_mul_const, fderiv_const_mul]
  · simp [fderiv_coordinateSum_power, smul_eq_mul]
    ring
  · exact ((coordinateSum_differentiable n).pow (k - 1)).differentiableAt
  · exact ((differentiable_const (k : ℂ)).mul ((coordinateSum_differentiable n).pow (k -
      1))).differentiableAt

theorem complexGinibrePregenerator_coordinateSum_power (n k : ℕ) (z : Configuration n) :
    complexGinibrePregenerator n (fun w => coordinateSum w ^ k) z =
      -(2 * (k : ℂ)) * coordinateSum z ^ k := by
  have hf : Differentiable ℝ (fun w : Configuration n => coordinateSum w ^ k) :=
    (coordinateSum_differentiable n).pow k
  have hdf (v : Configuration n) :
      Differentiable ℝ (fun w => fderiv ℝ (fun y => coordinateSum y ^ k) w v) := by
    simp_rw [fderiv_coordinateSum_power]
    exact (((coordinateSum_differentiable n).pow (k - 1)).const_mul _).mul_const _
  rw [complexGinibrePregenerator_eq_direct n _ hf hdf]
  unfold directComplexGinibrePregenerator
  simp only [coordinateSum_power_second, fderiv_coordinateSum_power,
    realCoordinateDirection, imaginaryCoordinateDirection, coordinateSum_coordinateDirection,
    coordinateSum_coulombPairDirection, pow_two, Complex.I_mul_I, mul_one,
    mul_neg, mul_zero, add_neg_cancel, Finset.sum_const_zero, zero_sub, add_zero]
  rw [← Finset.mul_sum]
  change -(2 * ((k : ℂ) * coordinateSum z ^ (k - 1) * coordinateSum z)) = _
  cases k with
  | zero => simp
  | succ k => simp [pow_succ]; ring

theorem coordinateSum_power_projectedGradient_memLp (n : ℕ) (hn : 0 < n)
    (k : ℕ) (T : ℂ →L[ℝ] ℝ) :
    MemLp (ginibreEuclideanGradient (fun z : Configuration n => T (coordinateSum z ^ k)))
      2 (ginibreMeasure n) := by
  apply memLp_piLp_iff.mpr
  intro j
  have hd := ((coordinateSum_power_memLp n hn (k - 1)).const_mul (k : ℂ)).mul_const
    (coordinateSum (ginibreCoordinateDirection j))
  have ht := T.comp_memLp' hd
  convert ht using 1
  funext z
  rw [ginibreEuclideanGradient_coordinate]
  have h := (T.hasFDerivAt.comp z
    ((coordinateSum_differentiable n).pow k z).hasFDerivAt).fderiv
  change (fderiv ℝ (T ∘ ((coordinateSum : Configuration n → ℂ) ^ k)) z)
    (ginibreCoordinateDirection j) = _
  rw [h]
  change T ((fderiv ℝ (fun w : Configuration n => coordinateSum w ^ k) z)
    (ginibreCoordinateDirection j)) = _
  rw [fderiv_coordinateSum_power]
  rfl

/-- The `k`-th power `(∑ i, z i) ^ k` of the coordinate sum, as an element of the symmetric
subspace of Ginibre `L²`. -/
def ginibreCoordinateSumPowerL2 (n : ℕ) (hn : 0 < n) (k : ℕ) : ginibreSymmetricL2 n :=
  ⟨(coordinateSum_power_memLp n hn k).toLp (fun z => coordinateSum z ^ k), by
    intro sigma
    apply Lp.ext
    have hc := (ginibre_measurePreserving_permute sigma).quasiMeasurePreserving.ae_eq_comp
      (coordinateSum_power_memLp n hn k).coeFn_toLp
    filter_upwards [Lp.coeFn_compMeasurePreserving
      ((coordinateSum_power_memLp n hn k).toLp (fun z => coordinateSum z ^ k))
      (ginibre_measurePreserving_permute sigma), hc,
      (coordinateSum_power_memLp n hn k).coeFn_toLp] with z hp hc hz
    change (Lp.compMeasurePreserving (permute sigma) (ginibre_measurePreserving_permute sigma)
      ((coordinateSum_power_memLp n hn k).toLp (fun z => coordinateSum z ^ k))) z = _
    rw [hp]
    simp only [Function.comp_apply] at hc ⊢
    rw [hc, hz, coordinateSum_permute]⟩

theorem ginibreCoordinateSumPowerL2_ae (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ((ginibreCoordinateSumPowerL2 n hn k).val : Configuration n → ℂ) =ᵐ[ginibreMeasure n]
      fun z => coordinateSum z ^ k :=
  (coordinateSum_power_memLp n hn k).coeFn_toLp

private theorem coordinateSum_power_projected_graph (n : ℕ) (hn : 0 < n) (k : ℕ)
    (T : ℂ →L[ℝ] ℝ) (U : ginibreFullSymmetricValues n)
    (hU : (U.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => T (coordinateSum z ^ k))
    (he : ∀ z, ginibrePregenerator n (fun w => T (coordinateSum w ^ k)) z =
      -(2 * (k : ℝ)) * T (coordinateSum z ^ k)) :
    (ginibreFullSymmetricOfReal n U,
      -(2 * (k : ℝ)) • ginibreFullSymmetricOfReal n U) ∈
      (ginibreFullGenerator n hn).graph := by
  have hg := coordinateSum_power_projectedGradient_memLp n hn k T
  let g := hg.toLp (ginibreEuclideanGradient (fun z => T (coordinateSum z ^ k)))
  have hf : ContDiff ℝ ∞ (fun z : Configuration n => T (coordinateSum z ^ k)) := by
    have hs : ContDiff ℝ ∞ (coordinateSum : Configuration n → ℂ) := by
      have heq : (coordinateSum : Configuration n → ℂ) = coordinateSumCLM n := by
        funext z; simp
      rw [heq]; exact (coordinateSumCLM n).contDiff
    exact T.contDiff.comp (hs.pow k)
  have hu := ginibre_smooth_distributional_gradient n hn U.val g _ hf hU hg.coeFn_toLp
  have hs : IsGinibreSymmetricWeakPair (U.val, g) := by
    intro sigma
    refine ⟨U.property sigma, ?_⟩
    have hp := ginibreDistributionalGradient_permute hn sigma U.val g hu
    rw [U.property sigma] at hp
    exact ginibre_distributional_gradient_unique n hn U.val _ _ hp hu
  have hv : ((-(2 * (k : ℝ)) • U).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      ginibrePregenerator n (fun z => T (coordinateSum z ^ k)) := by
    filter_upwards [Lp.coeFn_smul (-(2 * (k : ℝ))) U.val, hU] with z hz hu
    change (-(2 * (k : ℝ)) • U.val) z = _
    rw [hz]
    change -(2 * (k : ℝ)) * U.val z = _
    rw [hu]
    exact (he z).symm
  have hgraph := ginibreFullGenerator_smooth_graph hn _ hf U (-(2 * (k : ℝ)) • U)
    g hu hs hU hv
  simpa only [map_smul] using hgraph

theorem ginibreFullGenerator_coordinateSum_power_eigenpair (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (ginibreCoordinateSumPowerL2 n hn k,
      -(2 * (k : ℂ)) • ginibreCoordinateSumPowerL2 n hn k) ∈
      (ginibreFullGenerator n hn).graph := by
  let u := ginibreCoordinateSumPowerL2 n hn k
  have hr : ((ginibreFullSymmetricRe n u).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => (coordinateSum z ^ k).re := by
    filter_upwards [ginibreFullComplexRe_ae n u.val, ginibreCoordinateSumPowerL2_ae n hn k]
      with z h hpow
    change (ginibreFullComplexRe n u.val) z = _
    rw [h, hpow]
  have hi : ((ginibreFullSymmetricIm n u).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => (coordinateSum z ^ k).im := by
    filter_upwards [ginibreFullComplexIm_ae n u.val, ginibreCoordinateSumPowerL2_ae n hn k]
      with z h hpow
    change (ginibreFullComplexIm n u.val) z = _
    rw [h, hpow]
  have her (z : Configuration n) := congrArg Complex.re
    (complexGinibrePregenerator_coordinateSum_power n k z)
  have hei (z : Configuration n) := congrArg Complex.im
    (complexGinibrePregenerator_coordinateSum_power n k z)
  simp only [complexGinibrePregenerator, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, add_zero,
    sub_zero, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im,
    ] at her hei
  norm_num at her hei
  have hgr := coordinateSum_power_projected_graph n hn k Complex.reCLM _ hr
    (fun z => by simpa [neg_mul] using her z)
  have hgi := coordinateSum_power_projected_graph n hn k Complex.imCLM _ hi
    (fun z => by simpa [neg_mul] using hei z)
  let r := ginibreFullSymmetricOfReal n (ginibreFullSymmetricRe n u)
  let i := ginibreFullSymmetricOfReal n (ginibreFullSymmetricIm n u)
  have hd : r + Complex.I • i = u := by
    apply Subtype.ext
    exact ginibreFullComplex_decomposition n u.val
  have hgraph := (ginibreFullGenerator n hn).graph.add_mem hgr
    ((ginibreFullGenerator n hn).graph.smul_mem Complex.I hgi)
  have hp : (r, -(2 * (k : ℝ)) • r) + Complex.I • (i, -(2 * (k : ℝ)) • i) =
      (u, -(2 * (k : ℂ)) • u) := by
    apply Prod.ext
    · exact hd
    · change -(2 * (k : ℝ)) • r + Complex.I • (-(2 * (k : ℝ)) • i) = _
      rw [smul_comm Complex.I, ← smul_add]
      rw [hd]
      apply Subtype.ext
      simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [hp] at hgraph
  exact hgraph

/-- Exact nonzero norm of the Gaussian center powers in the interacting law. -/
theorem ginibreCoordinateSumPowerL2_norm_sq (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ‖ginibreCoordinateSumPowerL2 n hn k‖ ^ 2 = (k.factorial : ℝ) := by
  change ‖(ginibreCoordinateSumPowerL2 n hn k).val‖ ^ 2 = _
  rw [← integral_norm_sq_eq_L2_norm_sq]
  have he : (fun z => ‖(ginibreCoordinateSumPowerL2 n hn k).val z‖ ^ 2)
      =ᵐ[ginibreMeasure n] fun z => Complex.normSq (coordinateSum z) ^ k := by
    filter_upwards [ginibreCoordinateSumPowerL2_ae n hn k] with z hz
    rw [hz, norm_pow, Complex.normSq_eq_norm_sq]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
  rw [integral_congr_ae he]
  have hm := integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
    (Complex.continuous_normSq.pow k).aestronglyMeasurable
  change (∫ y : ℂ, Complex.normSq y ^ k ∂Measure.map coordinateSum (ginibreMeasure n)) =
    ∫ z : Configuration n, Complex.normSq (coordinateSum z) ^ k ∂ginibreMeasure n at hm
  rw [← hm, coordinateSum_ginibre_gaussian n hn]
  simpa [standardComplexGaussianMeasure] using integral_normSq_pow_coordinate 1 k (by decide)

/-- Corollary 1.5 at speed `n`, now including `n = 1`, on the exact full
symmetric Ginibre generator domain. -/
theorem ginibreFullGenerator_all_positive_n_spectrum_containment (n : ℕ) (hn : 0 < n) :
    {zeta : ℂ | ∃ k : ℕ, zeta = -(2 * (k : ℂ))} ⊆
      graphOperatorSpectrum (ginibreFullGenerator n hn) := by
  rintro zeta ⟨k, rfl⟩
  apply eigenpair_mem_graphOperatorSpectrum _ _ (ginibreCoordinateSumPowerL2 n hn k)
  · intro hz
    have hnorm := ginibreCoordinateSumPowerL2_norm_sq n hn k
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
    have hp : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    linarith
  · exact ginibreFullGenerator_coordinateSum_power_eigenpair n hn k

/-- Corollary 1.5 for every `n ≥ 1` and every positive paper speed. -/
theorem ginibreFullGeneratorAtSpeed_all_positive_n_spectrum_containment
    (n : ℕ) (hn : 0 < n) (alpha : ℝ) (_halpha : 0 < alpha) :
    {zeta : ℂ | ∃ k : ℕ, zeta = (-2 * (alpha / (n : ℝ)) * k : ℝ)} ⊆
      graphOperatorSpectrum (ginibreFullGeneratorAtSpeed n hn alpha) := by
  rintro zeta ⟨k, rfl⟩
  let u := ginibreCoordinateSumPowerL2 n hn k
  have hu : u ≠ 0 := by
    intro hz
    have hnorm := ginibreCoordinateSumPowerL2_norm_sq n hn k
    change ‖u‖ ^ 2 = _ at hnorm
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
    have hp : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    linarith
  apply eigenpair_mem_graphOperatorSpectrum _ _ u hu
  rw [ginibreFullGeneratorAtSpeed, LinearPMap.smul_graph]
  refine ⟨(u, -(2 * (k : ℂ)) • u),
    ginibreFullGenerator_coordinateSum_power_eigenpair n hn k, ?_⟩
  simp only [LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply]
  congr 1
  rw [smul_smul]
  congr 1
  push_cast
  ring

end
end GinibrePoincare
