/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/KostlanRadialTransfer.lean.
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

public import LeanPool.GinibrePoincare.Analysis.KostlanDiagonalIdentity
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar

/-! # Exact radial expectation transfer to a separable Gaussian weight
This identity is unconditional for bounded continuous symmetric radial tests.
The remaining Gamma-law/product-measure identification is separate.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace GinibrePoincare
noncomputable section

/-- The separable radial weight with exponents `0,...,n-1`. -/
def kostlanWeight (n : ℕ) (z : Configuration n) : ℝ :=
  ∏ i : Fin n, Complex.normSq (z i) ^ i.val

/-- Symmetry of a function of the individual squared radii. -/
def IsSymmetricRadiusTest (n : ℕ) (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (r : Fin n → ℝ), F (r ∘ σ) = F r

private theorem permuted_diagonal_integral (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : IsSymmetricRadiusTest n F) (σ : Equiv.Perm (Fin n)) :
    (∫ z : Configuration n, (F (fun i => Complex.normSq (z i)) : ℂ) *
      ∏ i, (Complex.normSq (z i) : ℂ) ^ (σ i).val ∂complexGaussianMeasure n) =
      ∫ z : Configuration n, (F (fun i => Complex.normSq (z i)) : ℂ) *
        (kostlanWeight n z : ℂ) ∂complexGaussianMeasure n := by
  let g : Configuration n → ℂ := fun z => (F (fun i => Complex.normSq (z i)) : ℂ) *
    (kostlanWeight n z : ℂ)
  have hmp : MeasurePreserving (permutationMeasurableEquiv σ.symm)
      (complexGaussianMeasure n) (complexGaussianMeasure n) := by
    have heq : (permutationMeasurableEquiv σ.symm : Configuration n → Configuration n) = permute
        σ.symm :=
      funext (permutationMeasurableEquiv_apply σ.symm)
    rw [heq]
    exact gaussian_measurePreserving_permute σ.symm
  have he := hmp.integral_comp' g
  have hfun (z : Configuration n) : g (permutationMeasurableEquiv σ.symm z) =
      (F (fun i => Complex.normSq (z i)) : ℂ) * ∏ i, (Complex.normSq (z i) : ℂ) ^ (σ i).val := by
    simp only [g, permutationMeasurableEquiv_apply, permute, kostlanWeight, Complex.ofReal_prod,
        Complex.ofReal_pow]
    have hs := hF σ.symm (fun i => Complex.normSq (z i))
    have hs' : F (fun i => Complex.normSq (z (σ.symm i))) = F (fun i => Complex.normSq (z i)) := hs
    rw [hs']
    congr 1
    simpa using (Equiv.prod_comp σ (fun i => (Complex.normSq (z (σ.symm i)) : ℂ) ^ i.val)).symm
  simpa only [hfun] using he

/-- The weighted Ginibre radial integral equals `n!` times the separable-weight integral. -/
theorem integral_radial_vandermonde_eq_factorial (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hS : IsSymmetricRadiusTest n F)
    (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫ z, vandermondeWeight z * F (fun i => Complex.normSq (z i)) ∂complexGaussianMeasure n) =
      (n.factorial : ℝ) * ∫ z, kostlanWeight n z * F (fun i => Complex.normSq (z i))
        ∂complexGaussianMeasure n := by
  have he := integral_radial_vandermonde_diagonal n hn F hF C hC
  simp_rw [permuted_diagonal_integral n F hS] at he
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      at he
  have hr := congrArg Complex.re he
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero, mul_comm] using
        hr

/-- An exact normalized radial expectation identity for the actual Ginibre measure. -/
theorem ginibre_radial_expectation_transfer (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hS : IsSymmetricRadiusTest n F)
    (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫ z, F (fun i => Complex.normSq (z i)) ∂ginibreMeasure n) =
      ((ginibreNormalizingMass n).toReal⁻¹ * (n.factorial : ℝ)) *
        ∫ z, kostlanWeight n z * F (fun i => Complex.normSq (z i)) ∂complexGaussianMeasure n := by
  rw [integral_ginibreMeasure, integral_radial_vandermonde_eq_factorial n hn F hF hS C hC]
  ring

/-- The explicit separable-weight reference law for individual radii. -/
def kostlanReference (n : ℕ) : Measure (Configuration n) :=
  ENNReal.ofReal ((ginibreNormalizingMass n).toReal⁻¹ * (n.factorial : ℝ)) •
    (complexGaussianMeasure n).withDensity (fun z => ENNReal.ofReal (kostlanWeight n z))

private theorem kostlanWeight_nonneg (n : ℕ) (z : Configuration n) : 0 ≤ kostlanWeight n z :=
  Finset.prod_nonneg fun _i _hi => pow_nonneg (Complex.normSq_nonneg _) _

private theorem integrable_kostlanWeight (n : ℕ) :
    Integrable (kostlanWeight n) (complexGaussianMeasure n) := by
  have he : kostlanWeight n = fun z : Configuration n => ∏ i, ‖z i‖ ^ (2*i.val) := by
    funext z
    unfold kostlanWeight
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Complex.sq_norm, ← pow_mul]
  rw [he]
  exact integrable_prod_norm_pow_complexGaussianMeasure n _

/-- The separable radial reference is an actual probability measure. -/
theorem kostlanReference_isProbabilityMeasure (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (kostlanReference n) := by
  have hprob := ginibreMeasure_isProbabilityMeasure hn
  have he := ginibre_radial_expectation_transfer n hn (fun _ => 1) continuous_const
    (fun σ r => rfl) 1 (by intro r; norm_num)
  simp only [integral_const, MeasureTheory.probReal_univ, one_smul, mul_one] at he
  have hc : 0 ≤ (ginibreNormalizingMass n).toReal⁻¹ * (n.factorial : ℝ) := by positivity
  constructor
  unfold kostlanReference
  rw [smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_kostlanWeight n)
      (Filter.Eventually.of_forall (kostlanWeight_nonneg n)), smul_eq_mul, ← ENNReal.ofReal_mul hc,
          ← he]
  simp

/-- Symmetric radial expectations under Ginibre equal those under the concrete reference law. -/
theorem ginibre_radial_expectation_eq_kostlanReference (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hS : IsSymmetricRadiusTest n F)
    (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫ z, F (fun i => Complex.normSq (z i)) ∂ginibreMeasure n) =
      ∫ z, F (fun i => Complex.normSq (z i)) ∂kostlanReference n := by
  rw [ginibre_radial_expectation_transfer n hn F hF hS C hC]
  unfold kostlanReference
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (kostlanWeight_nonneg _ _), smul_eq_mul]
  · unfold kostlanWeight
    fun_prop
  · exact Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top)

end
end GinibrePoincare
