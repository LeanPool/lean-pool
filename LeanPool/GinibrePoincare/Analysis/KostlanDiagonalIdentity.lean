/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/KostlanDiagonalIdentity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialGaussianOrthogonality
public import LeanPool.GinibrePoincare.Analysis.GaussianPolynomialIntegrability

/-! # The diagonal Vandermonde radial integral identity
For bounded continuous radial tests all off-diagonal determinant terms
vanish. This is the analytic cancellation behind Kostlan's identity.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Integrability of every mixed determinant term against a bounded radial test. -/
theorem integrable_radialMixedIntegrand (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) (a b : Fin n → ℕ) :
    Integrable (radialMixedIntegrand n F a b) (complexGaussianMeasure n) := by
  have hm : AEStronglyMeasurable (radialMixedIntegrand n F a b) (complexGaussianMeasure n) := by
    apply Continuous.aestronglyMeasurable
    unfold radialMixedIntegrand
    fun_prop
  apply ((integrable_prod_norm_pow_complexGaussianMeasure n (fun i => a i + b i)).const_mul C).mono'
      hm
  filter_upwards with z
  simp only [radialMixedIntegrand, norm_mul, Complex.norm_real, norm_prod, norm_pow,
      Complex.norm_conj, ← pow_add]
  exact mul_le_mul_of_nonneg_right (hC _) (Finset.prod_nonneg fun i hi =>
    pow_nonneg (norm_nonneg (z i)) (a i + b i))

private def detTerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : Configuration n) : ℂ :=
  (Equiv.Perm.sign σ : ℂ) * ∏ i, z i ^ (σ i).val

private theorem vandermonde_sum (n : ℕ) (z : Configuration n) :
    vandermonde z = ∑ σ : Equiv.Perm (Fin n), detTerm σ z := by
  unfold vandermonde
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

/-- Exact angular cancellation of the Vandermonde square against radial tests. -/
theorem integral_radial_vandermonde_diagonal (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫ z : Configuration n, (F (fun i => Complex.normSq (z i)) : ℂ) *
      (vandermondeWeight z : ℂ) ∂complexGaussianMeasure n) =
      ∑ σ : Equiv.Perm (Fin n), ∫ z : Configuration n,
        (F (fun i => Complex.normSq (z i)) : ℂ) *
          ∏ i, (Complex.normSq (z i) : ℂ) ^ (σ i).val ∂complexGaussianMeasure n := by
  classical
  have hex (z : Configuration n) : (F (fun i => Complex.normSq (z i)) : ℂ) *
      (vandermondeWeight z : ℂ) = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℂ) * conj (Equiv.Perm.sign τ : ℂ)) *
          radialMixedIntegrand n F (fun i => (σ i).val) (fun i => (τ i).val) z := by
    rw [show (vandermondeWeight z : ℂ) = vandermonde z * conj (vandermonde z) by
      exact (Complex.mul_conj _).symm]
    rw [vandermonde_sum, map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro τ hτ
    simp only [detTerm, map_mul, map_prod, map_pow, radialMixedIntegrand]
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hex]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro σ hσ
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
      rw [Finset.sum_eq_single σ]
      · have hp : (Equiv.Perm.sign σ : ℂ) * conj (Equiv.Perm.sign σ : ℂ) = 1 := by
          simp only [map_intCast]
          norm_cast
          exact congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_mul_self (Equiv.Perm.sign σ))
        rw [hp, one_mul]
        apply integral_congr_ae
        filter_upwards with z
        unfold radialMixedIntegrand
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [← mul_pow, Complex.mul_conj]
      · intro τ hτ hτσ
        have hne : (fun i => (σ i).val) ≠ (fun i => (τ i).val) := by
          intro he
          apply hτσ
          apply Equiv.ext
          intro i
          exact Fin.ext ((congrFun he i).symm)
        rw [integral_radialMixedIntegrand_eq_zero n hn F _ _ hne, mul_zero]
      · simp
    · intro τ hτ
      exact (integrable_radialMixedIntegrand n F hF C hC _ _).const_mul _
  · intro σ hσ
    apply integrable_finsetSum
    intro τ hτ
    exact (integrable_radialMixedIntegrand n F hF C hC _ _).const_mul _

end
end GinibrePoincare
