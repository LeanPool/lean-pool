/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianRadialLift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianBlockRadialLaw

/-!
# Gaussian radial lift

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `radial_lsi_iff_gaussian_lift`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- Euclidean gradient energy on the independent complex blocks. -/
def blockGradientNormSq {n : ℕ} (H : GaussianRadialBlocks n → ℝ)
    (x : GaussianRadialBlocks n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin (i.val + 1),
    ((fderiv ℝ H x (Pi.single i (realCoordinateDirection j))) ^ 2 +
      (fderiv ℝ H x (Pi.single i (imaginaryCoordinateDirection j))) ^ 2)

/-- The real-linear projection of the block lift onto the `j`-th complex coordinate of its
`i`-th block. -/
def blockCoordinateProjection (n : ℕ) (i : Fin n) (j : Fin (i.val + 1)) :
    GaussianRadialBlocks n →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : Configuration (i.val + 1) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : GaussianRadialBlocks n →L[ℝ] Configuration (i.val + 1))

/-- The Fréchet derivative at `x` of the block radii `gaussianBlockRadii n`: its `i`-th component
is `∑ j 2n (Re (x i j) · Re + Im (x i j) · Im)` applied to the `i`-th block. -/
def blockRadiusDerivative (n : ℕ) (x : GaussianRadialBlocks n) :
    GaussianRadialBlocks n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => ∑ j : Fin (i.val + 1),
    ((2 * (n : ℝ) * (x i j).re) •
      (Complex.reCLM.comp (blockCoordinateProjection n i j)) +
    (2 * (n : ℝ) * (x i j).im) •
      (Complex.imCLM.comp (blockCoordinateProjection n i j))))

theorem hasFDerivAt_blockRadii (n : ℕ) (x : GaussianRadialBlocks n) :
    HasFDerivAt (gaussianBlockRadii n) (blockRadiusDerivative n x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hd (j : Fin (i.val + 1)) :
      HasFDerivAt (fun y : GaussianRadialBlocks n => (n : ℝ) * Complex.normSq (y i j))
        ((2 * (n : ℝ) * (x i j).re) •
          (Complex.reCLM.comp (blockCoordinateProjection n i j)) +
         (2 * (n : ℝ) * (x i j).im) •
          (Complex.imCLM.comp (blockCoordinateProjection n i j))) x := by
    have hr := Complex.reCLM.hasFDerivAt.comp x
      (blockCoordinateProjection n i j).hasFDerivAt
    have hi := Complex.imCLM.hasFDerivAt.comp x
      (blockCoordinateProjection n i j).hasFDerivAt
    have h := ((hr.mul hr).add (hi.mul hi)).const_mul (n : ℝ)
    convert! h using 1
    ext v
    simp [blockCoordinateProjection]
    ring
  have h := HasFDerivAt.sum (u := Finset.univ) (fun j _ => hd j)
  convert! h using 1
  funext y
  simp [gaussianBlockRadii, gaussianBlockRadius, configurationNormSq, Finset.mul_sum]

private theorem blockRadiusDerivative_direction (n : ℕ) (x : GaussianRadialBlocks n)
    (i : Fin n) (j : Fin (i.val + 1)) (w : ℂ) :
    blockRadiusDerivative n x (Pi.single i (coordinateDirection j w)) =
      (2 * (n : ℝ) * ((x i j).re * w.re + (x i j).im * w.im)) •
        (Pi.single i 1 : Fin n → ℝ) := by
  ext k
  by_cases hk : k = i
  · subst k
    simp only [blockRadiusDerivative, blockCoordinateProjection,
      ContinuousLinearMap.coe_pi', sum_apply, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
      coordinateDirection, Complex.reCLM_apply, smul_eq_mul, Complex.imCLM_apply,
      Pi.smul_apply, mul_one]
    rw [Finset.sum_eq_single j]
    · simp
      ring
    · intro b hb hbj
      simp [hbj]
    · intro h
      simp at h
  · simp [blockRadiusDerivative, blockCoordinateProjection, hk]

/-- The Gaussian lift has exactly the same Gamma-coordinate gradient density. -/
theorem blockGradientNormSq_radial (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : Differentiable ℝ F) (x : GaussianRadialBlocks n) :
    blockGradientNormSq (fun x => F (gaussianBlockRadii n x)) x =
      (n : ℝ) * gammaRadialEnergyDensity F (gaussianBlockRadii n x) := by
  have hd := ((hF _).hasFDerivAt.comp x (hasFDerivAt_blockRadii n x)).fderiv
  change fderiv ℝ (fun x => F (gaussianBlockRadii n x)) x = _ at hd
  unfold blockGradientNormSq
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, realCoordinateDirection,
    imaginaryCoordinateDirection, blockRadiusDerivative_direction, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
    map_smul, smul_eq_mul]
  unfold gammaRadialEnergyDensity radiusPartial
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold gaussianBlockRadii gaussianBlockRadius configurationNormSq
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.normSq_apply]
  ring

/-- Equality of entropy between the actual Ginibre radial observable and its Gaussian lift. -/
theorem ginibre_radial_entropy_eq_block (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hc : HasCompactSupport F)
    (hS : IsSymmetricRadiusTest n F) :
    ginibreSquareEntropy n (fun z => F (scaledSquaredRadii n z)) =
      squareEntropy (gaussianRadialBlockMeasure n) (fun x => F (gaussianBlockRadii n x)) := by
  change ginibreSquareEntropy n (fun z => F (fun i => kostlanSquaredRadius n (z i))) = _
  rw [ginibre_radial_entropy_eq_gamma_product n hn F hF hc hS,
    ← gaussianRadialBlockMeasure_map n hn]
  apply squareEntropy_map
  · apply Measurable.aemeasurable
    unfold gaussianBlockRadii gaussianBlockRadius configurationNormSq
    fun_prop
  · exact (hF.pow 2).aestronglyMeasurable
  · exact (continuous_square_mul_log hF).aestronglyMeasurable

/-- Equality of the normalized Euclidean energies on Ginibre and Gaussian blocks. -/
theorem ginibre_radial_energy_eq_block (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hS : IsSymmetricRadiusTest n F) :
    smoothGinibreEnergy n (fun z => F (scaledSquaredRadii n z)) =
      (1 / (n : ℝ)) * ∫ x, blockGradientNormSq
        (fun x => F (gaussianBlockRadii n x)) x ∂gaussianRadialBlockMeasure n := by
  rw [smoothGinibreEnergy_radial_eq_gamma n hn F hF hc hS]
  simp_rw [blockGradientNormSq_radial n F (hF.differentiable (by simp))]
  rw [integral_const_mul, ← mul_assoc, one_div,
    inv_mul_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_mul,
    ← gaussianRadialBlockMeasure_map n hn]
  have hq : Measurable (gaussianBlockRadii n) := by
    unfold gaussianBlockRadii gaussianBlockRadius configurationNormSq
    fun_prop
  exact integral_map hq.aemeasurable (gammaRadialEnergyDensity_regular F hF
      hc).1.aestronglyMeasurable

/-- An exact equivalence of the radial inequalities, not a proof of Gaussian LSI. -/
theorem radial_lsi_iff_gaussian_lift (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hS : IsSymmetricRadiusTest n F) :
    (ginibreSquareEntropy n (fun z => F (scaledSquaredRadii n z)) ≤
      smoothGinibreEnergy n (fun z => F (scaledSquaredRadii n z))) ↔
    (squareEntropy (gaussianRadialBlockMeasure n) (fun x => F (gaussianBlockRadii n x)) ≤
      (1 / (n : ℝ)) * ∫ x, blockGradientNormSq
        (fun x => F (gaussianBlockRadii n x)) x ∂gaussianRadialBlockMeasure n) := by
  rw [ginibre_radial_entropy_eq_block n hn F hF.continuous hc hS,
    ginibre_radial_energy_eq_block n hn F hF hc hS]

end
end GinibrePoincare
