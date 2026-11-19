/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialEquilibriumOrthogonality.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialEigenfunctions
public import LeanPool.GinibrePoincare.Analysis.LaguerreGammaOrthogonality
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarParseval
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L2Space
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianProductIntegral
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation

/-! # Equilibrium orthogonality of the concrete Hermite–Laguerre family
The Gaussian sum and Gamma radius are independent. All inner-product
integrands below are integrable; orthogonality is for the actual Ginibre law.
The classical Laguerre factor is not normalized to have unit norm.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

private theorem measurable_pairwiseRadius (n : ℕ) :
    Measurable (pairwiseRadius : Configuration n → ℝ) := by
  unfold pairwiseRadius
  fun_prop

private theorem radius_gamma_nat (n : ℕ) (hn : 2 ≤ n) :
    (ginibreMeasure n).map pairwiseRadius = gammaMeasure (recenteredGammaShape n : ℝ) 1 := by
  rw [recenteredGammaShape_eq n (by omega)]
  exact pairwiseRadius_ginibre_gamma n hn

/-- Independent polynomial-coordinate factors have integrable products. -/
theorem integrable_sum_radius_product (n : ℕ) (hn : 2 ≤ n)
    (f : ℂ → ℂ) (g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable f standardComplexGaussianMeasure)
    (hgi : Integrable g (gammaMeasure (recenteredGammaShape n : ℝ) 1)) :
    Integrable (fun z : Configuration n => f (coordinateSum z) * g (pairwiseRadius z))
      (ginibreMeasure n) := by
  have hfm : Integrable f ((ginibreMeasure n).map coordinateSum) := by
    rw [coordinateSum_ginibre_gaussian n (by omega)]; exact hfi
  have hgm : Integrable g ((ginibreMeasure n).map pairwiseRadius) := by
    rw [radius_gamma_nat n hn]; exact hgi
  have hfc := (integrable_map_measure hf.aestronglyMeasurable
    (measurable_coordinateSum n).aemeasurable).mp hfm
  have hgc := (integrable_map_measure hg.aestronglyMeasurable
    (measurable_pairwiseRadius n).aemeasurable).mp hgm
  exact ((coordinateSum_pairwiseRadius_indepFun n (by omega)).comp
    hf.measurable hg.measurable).integrable_mul hfc hgc

/-- The actual equilibrium integral separates into its Gaussian and Gamma factors. -/
theorem integral_sum_radius_product (n : ℕ) (hn : 2 ≤ n)
    (f : ℂ → ℂ) (g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ z : Configuration n, f (coordinateSum z) * g (pairwiseRadius z) ∂ginibreMeasure n) =
      (∫ s, f s ∂standardComplexGaussianMeasure) *
        (∫ r, g r ∂gammaMeasure (recenteredGammaShape n : ℝ) 1) := by
  rw [(coordinateSum_pairwiseRadius_indepFun n (by omega)).integral_fun_comp_mul_comp
    (measurable_coordinateSum n).aemeasurable (measurable_pairwiseRadius n).aemeasurable
    hf.aestronglyMeasurable hg.aestronglyMeasurable]
  rw [← integral_map (measurable_coordinateSum n).aemeasurable hf.aestronglyMeasurable,
    ← integral_map (measurable_pairwiseRadius n).aemeasurable hg.aestronglyMeasurable,
    coordinateSum_ginibre_gaussian n (by omega), radius_gamma_nat n hn]

private def hermiteInner (a b c d : ℕ) (s : ℂ) : ℂ :=
  conj (ComplexHermite.normalizedEval 1 (by decide) a b s) *
    ComplexHermite.normalizedEval 1 (by decide) c d s

private def laguerreInner (k m l : ℕ) (r : ℝ) : ℂ :=
  ((Laguerre.polynomial k m).eval r * (Laguerre.polynomial k l).eval r : ℝ)

private theorem continuous_hermiteInner (a b c d : ℕ) : Continuous (hermiteInner a b c d) :=
  (Complex.continuous_conj.comp (ComplexHermite.continuous_normalizedEval 1 (by decide) a b)).mul
    (ComplexHermite.continuous_normalizedEval 1 (by decide) c d)

private theorem continuous_laguerreInner (k m l : ℕ) : Continuous (laguerreInner k m l) := by
  unfold laguerreInner
  fun_prop

private theorem eigenfunction_inner_eq (n a b m c d l : ℕ) (z : Configuration n) :
    conj (polynomialEigenfunction n ⟨a, b, m⟩ z) * polynomialEigenfunction n ⟨c, d, l⟩ z =
      hermiteInner a b c d (coordinateSum z) *
        laguerreInner (recenteredGammaShape n) m l (pairwiseRadius z) := by
  simp only [polynomialEigenfunction, SObservable, RPoly, map_mul,
    Complex.conj_ofReal, hermiteInner, laguerreInner, Complex.ofReal_mul]
  ring

/-- Every pair of concrete eigenfunctions has an integrable equilibrium inner product. -/
theorem integrable_polynomialEigenfunction_inner (n : ℕ) (hn : 2 ≤ n)
    (a b m c d l : ℕ) :
    Integrable (fun z : Configuration n => conj (polynomialEigenfunction n ⟨a, b, m⟩ z) *
      polynomialEigenfunction n ⟨c, d, l⟩ z) (ginibreMeasure n) := by
  simp_rw [eigenfunction_inner_eq]
  exact integrable_sum_radius_product n hn _ _ (continuous_hermiteInner a b c d)
    (continuous_laguerreInner _ m l)
    (ComplexHermite.integrable_conj_normalizedEval_mul 1 (by decide) a b c d)
    (Laguerre.integrable_polynomial_mul _ m l (recenteredGammaShape_pos n hn)).ofReal

/-- The exact equilibrium inner product reduces to the classical Laguerre inner product. -/
theorem integral_polynomialEigenfunction_inner (n : ℕ) (hn : 2 ≤ n)
    (a b m c d l : ℕ) :
    (∫ z : Configuration n, conj (polynomialEigenfunction n ⟨a, b, m⟩ z) *
      polynomialEigenfunction n ⟨c, d, l⟩ z ∂ginibreMeasure n) =
      (if a = c ∧ b = d then (1 : ℂ) else 0) *
        (Complex.ofReal (∫ r : ℝ, (Laguerre.polynomial (recenteredGammaShape n) m).eval r *
          (Laguerre.polynomial (recenteredGammaShape n) l).eval r
          ∂gammaMeasure (recenteredGammaShape n : ℝ) 1)) := by
  simp_rw [eigenfunction_inner_eq]
  rw [integral_sum_radius_product n hn _ _ (continuous_hermiteInner a b c d)
    (continuous_laguerreInner _ m l)]
  have hH : (∫ s, hermiteInner a b c d s ∂standardComplexGaussianMeasure) =
      if a = c ∧ b = d then (1 : ℂ) else 0 := by
    simpa only [hermiteInner, standardComplexGaussianMeasure, mul_comm, eq_comm] using
      integral_normalizedEval_mul_conj_normalizedEval 1 (by decide) c d a b
  rw [hH]
  congr 1
  exact integral_ofReal

/-- Distinct Hermite–Laguerre indices are orthogonal under the actual Ginibre law. -/
theorem polynomialEigenfunction_equilibrium_orthogonal (n : ℕ) (hn : 2 ≤ n)
    (a b m c d l : ℕ) (hindices : ¬ (a = c ∧ b = d ∧ m = l)) :
    (∫ z : Configuration n, conj (polynomialEigenfunction n ⟨a, b, m⟩ z) *
      polynomialEigenfunction n ⟨c, d, l⟩ z ∂ginibreMeasure n) = 0 := by
  rw [integral_polynomialEigenfunction_inner n hn]
  split_ifs with hab
  · have hml : m ≠ l := by intro he; exact hindices ⟨hab.1, hab.2, he⟩
    rw [Laguerre.integral_polynomial_mul_eq_zero _ m l (recenteredGammaShape_pos n hn) hml]
    simp
  · simp

/-- Every member of the concrete family belongs to equilibrium `L²`. -/
theorem polynomialEigenfunction_memLp_two (n : ℕ) (hn : 2 ≤ n) (a b m : ℕ) :
    MemLp (polynomialEigenfunction n ⟨a, b, m⟩) 2 (ginibreMeasure n) := by
  have hc : Continuous (polynomialEigenfunction n ⟨a, b, m⟩) := by
    have hH := ComplexHermite.continuous_normalizedEval 1 (by decide) a b
    unfold polynomialEigenfunction SObservable RPoly coordinateSum pairwiseRadius
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := (integrable_polynomialEigenfunction_inner n hn a b m a b m).re
  convert hi using 1
  funext z
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]

end
end GinibrePoincare
