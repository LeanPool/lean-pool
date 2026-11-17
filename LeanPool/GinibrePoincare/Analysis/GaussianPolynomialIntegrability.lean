/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianPolynomialIntegrability.lean.
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

public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import LeanPool.GinibrePoincare.Analysis.HermiteWirtinger

/-! # Polynomial integrability under the Ginibre Gaussian reference law -/


@[expose] public section


open MeasureTheory
open scoped ENNReal BigOperators ComplexConjugate

namespace GinibrePoincare

noncomputable section

/-- The complex-coordinate law is a Gaussian measure on the underlying real
Banach space. -/
theorem isGaussian_complexCoordinateGaussianProbability (n : ℕ) :
    ProbabilityTheory.IsGaussian
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  let g : Measure ℝ := realCoordinateGaussianProbability n
  have hg : ProbabilityTheory.IsGaussian g := by
    unfold g realCoordinateGaussianProbability
    simp only [ProbabilityMeasure.coe_mk]
    infer_instance
  have hprod : ProbabilityTheory.IsGaussian (g.prod g) := by
    let : ProbabilityTheory.IsGaussian g := hg
    infer_instance
  have hsource :
      (Measure.pi (fun _ : Fin 2 ↦ g)).map MeasurableEquiv.finTwoArrow =
        g.prod g :=
    (measurePreserving_finTwoArrow g).map_eq
  unfold complexCoordinateGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi]
  rw [show Complex.measurableEquivPi.symm =
      Complex.equivRealProdCLM.symm ∘ MeasurableEquiv.finTwoArrow by
    funext x
    apply Complex.ext <;> simp [MeasurableEquiv.finTwoArrow]]
  have heq :
      (Measure.pi (fun _ : Fin 2 ↦ g)).map
          (Complex.equivRealProdCLM.symm ∘ MeasurableEquiv.finTwoArrow) =
        (g.prod g).map Complex.equivRealProdCLM.symm := by
    rw [← hsource]
    exact (Measure.map_map
      (μ := Measure.pi (fun _ : Fin 2 ↦ g))
      Complex.equivRealProdCLM.symm.continuous.measurable
      MeasurableEquiv.finTwoArrow.measurable).symm
  change ProbabilityTheory.IsGaussian
    ((Measure.pi (fun _ : Fin 2 ↦ g)).map
      (Complex.equivRealProdCLM.symm ∘ MeasurableEquiv.finTwoArrow))
  rw [heq]
  let : ProbabilityTheory.IsGaussian (g.prod g) := hprod
  infer_instance

/-- Every finite power of the norm of one complex Gaussian coordinate is
integrable. -/
theorem integrable_norm_pow_complexCoordinateGaussianProbability
    (n k : ℕ) :
    Integrable (fun z : ℂ ↦ ‖z‖ ^ k)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  let : ProbabilityTheory.IsGaussian
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
    isGaussian_complexCoordinateGaussianProbability n
  exact (ProbabilityTheory.IsGaussian.memLp_id
    (complexCoordinateGaussianProbability n : Measure ℂ) k (by simp)).integrable_norm_pow'

/-- Every mixed complex monomial is integrable under one coordinate of the
Gaussian reference law. -/
theorem integrable_pow_mul_conj_pow_complexCoordinateGaussianProbability
    (n a b : ℕ) :
    Integrable (fun z : ℂ ↦ z ^ a * conj z ^ b)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  have hm : AEStronglyMeasurable (fun z : ℂ ↦ z ^ a * conj z ^ b)
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
    ((continuous_id.pow a).mul (Complex.continuous_conj.pow b)).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  convert integrable_norm_pow_complexCoordinateGaussianProbability n (a + b) using 1
  funext z
  simp [norm_pow, pow_add]

theorem integrable_const_mul_pow_mul_conj_pow_complexCoordinateGaussianProbability
    (n a b : ℕ) (c : ℂ) :
    Integrable (fun z : ℂ ↦ c * (z ^ a * conj z ^ b))
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
  (integrable_pow_mul_conj_pow_complexCoordinateGaussianProbability n a b).const_mul c

/-- The diagonal evaluation of every two-variable complex polynomial is
integrable under one complex Gaussian coordinate. -/
theorem integrable_mvPolynomial_diagonalEval (n : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun z : ℂ ↦ MvPolynomial.eval ![z, conj z] P)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [MvPolynomial.as_sum P]
  simp_rw [MvPolynomial.eval_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro d hd
  have heval : (fun z : ℂ ↦ d.prod fun i e ↦ (![z, conj z] i) ^ e) =
      fun z : ℂ ↦ z ^ d 0 * conj z ^ d 1 := by
    funext z
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]
    · intro i
      simp
  exact (integrable_const_mul_pow_mul_conj_pow_complexCoordinateGaussianProbability
      n (d 0) (d 1) (P.coeff d)).congr
    (Filter.Eventually.of_forall fun z =>
      congrArg (fun w : ℂ => P.coeff d * w) (congrFun heval z).symm)

theorem integrable_mul_mvPolynomial_diagonalEval (n : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun z : ℂ ↦ z * MvPolynomial.eval ![z, conj z] P)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  exact (integrable_mvPolynomial_diagonalEval n (MvPolynomial.X 0 * P)).congr
    (Filter.Eventually.of_forall fun z => by simp [MvPolynomial.eval_mul])

theorem integrable_conj_mul_mvPolynomial_diagonalEval (n : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun z : ℂ ↦ conj z * MvPolynomial.eval ![z, conj z] P)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  exact (integrable_mvPolynomial_diagonalEval n (MvPolynomial.X 1 * P)).congr
    (Filter.Eventually.of_forall fun z => by simp [MvPolynomial.eval_mul])

theorem integrable_pderiv_Z_mvPolynomial_diagonalEval (n : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun z : ℂ ↦
      MvPolynomial.eval ![z, conj z] (MvPolynomial.pderiv 0 P))
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
  integrable_mvPolynomial_diagonalEval n (MvPolynomial.pderiv 0 P)

theorem integrable_pderiv_W_mvPolynomial_diagonalEval (n : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun z : ℂ ↦
      MvPolynomial.eval ![z, conj z] (MvPolynomial.pderiv 1 P))
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
  integrable_mvPolynomial_diagonalEval n (MvPolynomial.pderiv 1 P)

theorem integrable_mul_mvPolynomial_diagonalEval_two (n : ℕ)
    (P Q : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun z : ℂ ↦ MvPolynomial.eval ![z, conj z] P *
      MvPolynomial.eval ![z, conj z] Q)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  exact (integrable_mvPolynomial_diagonalEval n (P * Q)).congr
    (Filter.Eventually.of_forall fun z => by simp [MvPolynomial.eval_mul])

theorem integrable_fderiv_mvPolynomial_diagonalEval (n : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) (v : ℂ) :
    Integrable (fun z : ℂ ↦
      (fderiv ℝ (fun w : ℂ ↦ MvPolynomial.eval ![w, conj w] P) z) v)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  obtain ⟨Q, hQ⟩ := ComplexHermite.exists_fderiv_diagonalEval_polynomial P v
  exact (integrable_mvPolynomial_diagonalEval n Q).congr
    (Filter.Eventually.of_forall fun z => (hQ z).symm)

theorem integrable_fderiv_one_mvPolynomial_diagonalEval (n : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun z : ℂ ↦
      (fderiv ℝ (fun w : ℂ ↦ MvPolynomial.eval ![w, conj w] P) z) 1)
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
  integrable_fderiv_mvPolynomial_diagonalEval n P 1

theorem integrable_fderiv_I_mvPolynomial_diagonalEval (n : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun z : ℂ ↦
      (fderiv ℝ (fun w : ℂ ↦ MvPolynomial.eval ![w, conj w] P) z) Complex.I)
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
  integrable_fderiv_mvPolynomial_diagonalEval n P Complex.I

/-- Products of arbitrary coordinate norm powers are integrable under the
finite product complex Gaussian law. -/
theorem integrable_prod_norm_pow_complexGaussianMeasure (n : ℕ)
    (k : Fin n → ℕ) :
    Integrable (fun z : Configuration n ↦ ∏ i, ‖z i‖ ^ k i)
      (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  exact Integrable.fintype_prod fun i ↦
    integrable_norm_pow_complexCoordinateGaussianProbability n (k i)

/-- In particular, any common coordinate norm power has an integrable product
under the finite product complex Gaussian law. -/
theorem integrable_prod_norm_pow_const_complexGaussianMeasure (n k : ℕ) :
    Integrable (fun z : Configuration n ↦ ∏ i, ‖z i‖ ^ k)
      (complexGaussianMeasure n) :=
  integrable_prod_norm_pow_complexGaussianMeasure n (fun _ ↦ k)

end

end GinibrePoincare
