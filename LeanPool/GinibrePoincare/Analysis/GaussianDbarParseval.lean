/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDbarParseval.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteParsevalModes
public import LeanPool.GinibrePoincare.Analysis.HermiteEnergy
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar

/-! # Gaussian `dbar` energy and Hermite modes -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

namespace GinibrePoincare

noncomputable section

open ComplexHermite

theorem complexGaussianDbarIntegrationByParts_of_integrable
    {n : ℕ} (hn : 0 < n) {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hFi : Integrable F (complexCoordinateGaussianProbability n : Measure ℂ))
    (hDr : Integrable (fun z ↦ (fderiv ℝ F z) (1 : ℂ))
      (complexCoordinateGaussianProbability n : Measure ℂ))
    (hDi : Integrable (fun z ↦ (fderiv ℝ F z) Complex.I)
      (complexCoordinateGaussianProbability n : Measure ℂ))
    (hX : Integrable (fun z ↦ (z.re : ℂ) * F z)
      (complexCoordinateGaussianProbability n : Measure ℂ))
    (hY : Integrable (fun z ↦ (z.im : ℂ) * F z)
      (complexCoordinateGaussianProbability n : Measure ℂ)) :
    (∫ z, dbarOnePublic F z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (n : ℂ) * ∫ z, z * F z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  unfold dbarOnePublic dbarOne
  rw [integral_const_mul, integral_add hDr (hDi.const_mul Complex.I),
    integral_const_mul,
    complexGaussianIntegrationByParts_real_of_integrable hn hF hFi hDr hX,
    complexGaussianIntegrationByParts_imag_of_integrable hn hF hFi hDi hY]
  have hz : (fun z : ℂ ↦ (z.re : ℂ) * F z +
      Complex.I * ((z.im : ℂ) * F z)) = fun z ↦ z * F z := by
    funext z
    apply Complex.ext <;> simp ; ring
  have hint : (∫ z, z * F z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (∫ z, (z.re : ℂ) * F z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ)) +
      Complex.I * ∫ z, (z.im : ℂ) * F z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
    rw [← integral_const_mul, ← integral_add hX (hY.const_mul Complex.I), hz]
  rw [hint]
  push_cast
  ring

theorem complexGaussianDbarIntegrationByParts_diagonalEval
    {n : ℕ} (hn : 0 < n) (P : Poly) :
    (∫ z, dbarOnePublic (diagonalEvalPublic P) z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (n : ℂ) * ∫ z, z * diagonalEvalPublic P z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  obtain ⟨R, hR⟩ := exists_fderiv_diagonalEvalPublic_polynomial P 1
  obtain ⟨S, hS⟩ := exists_fderiv_diagonalEvalPublic_polynomial P Complex.I
  have hz := integrable_mul_mvPolynomial_diagonalEval n P
  have hcz := integrable_conj_mul_mvPolynomial_diagonalEval n P
  apply complexGaussianDbarIntegrationByParts_of_integrable hn
    (contDiff_diagonalEvalPublic P)
    (integrable_mvPolynomial_diagonalEval n P)
  · exact (integrable_mvPolynomial_diagonalEval n R).congr
      (Filter.Eventually.of_forall fun z ↦ (hR z).symm)
  · exact (integrable_mvPolynomial_diagonalEval n S).congr
      (Filter.Eventually.of_forall fun z ↦ (hS z).symm)
  · apply ((hz.add hcz).const_mul (1 / 2 : ℂ)).congr
    filter_upwards with z
    simp only [diagonalEvalPublic, diagonalEval]
    apply Complex.ext <;> simp <;> ring
  · apply ((hz.sub hcz).const_mul (1 / (2 * Complex.I) : ℂ)).congr
    filter_upwards with z
    simp only [diagonalEvalPublic, diagonalEval]
    apply Complex.ext <;> simp <;> ring

theorem integrable_normalizedEval_complexGaussian (n : ℕ) (hn : 0 < n)
    (p q : ℕ) :
    Integrable (normalizedEval n hn p q)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  exact ComplexHermite.integrable_normalizedEval n hn p q

theorem integrable_normalizedEval_lowering_complexGaussian
    (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    Integrable (fun z ↦ (Real.sqrt (n * q : ℕ) : ℂ) *
      normalizedEval n hn p (q - 1) z)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  exact (integrable_normalizedEval_complexGaussian n hn p (q - 1)).const_mul _

theorem integrable_coordinate_mul_normalizedEval_complexGaussian
    (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    Integrable (fun z : ℂ ↦ z * normalizedEval n hn p q z)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  have hprod := ComplexHermite.integrable_normalizedEval_mul n hn 1 0 p q
  have hsqrt : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hsqrtC : (Real.sqrt n : ℂ) ≠ 0 := by exact_mod_cast hsqrt
  have hscaled := hprod.const_mul ((Real.sqrt n : ℂ)⁻¹)
  apply hscaled.congr
  filter_upwards with z
  rw [normalizedEval_zero_right]
  rw [show oneDimNormalization n 1 = Real.sqrt n by
    simp [oneDimNormalization]]
  simp only [pow_one]
  field_simp [hsqrtC]

private theorem mixedMomentFormula_of_pos (n : ℕ) (hn : 0 < n) :
    MixedMomentFormula n := by
  intro a b
  rw [show (∫ z : ℂ, z ^ a * conj z ^ b
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      complexGaussianMixedMoment n a b by rfl]
  rw [complexGaussianMixedMoment_formula hn]
  simp [div_eq_mul_inv]

theorem integral_normalizedEval_complexGaussian (n : ℕ) (hn : 0 < n)
    (p q : ℕ) :
    (∫ z : ℂ, normalizedEval n hn p q z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      if p = 0 ∧ q = 0 then 1 else 0 := by
  have horth := normalizedEval_orthogonal_of_mixedMoments n hn
    (mixedMomentFormula_of_pos n hn) 0 0 p q
  simpa [eq_comm] using horth

theorem sqrt_mul_integral_coordinate_mul_normalizedEval
    (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    (Real.sqrt n : ℂ) *
        (∫ z : ℂ, z * normalizedEval n hn p q z
          ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      if p = 0 ∧ q = 1 then 1 else 0 := by
  rw [← integral_const_mul]
  have horth := normalizedEval_orthogonal_of_mixedMoments n hn
    (mixedMomentFormula_of_pos n hn) 0 1 p q
  have horth' : (∫ z : ℂ, conj (normalizedEval n hn 0 1 z) *
      normalizedEval n hn p q z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      if p = 0 ∧ q = 1 then 1 else 0 := by simpa [eq_comm] using horth
  rw [← horth']
  apply integral_congr_ae
  filter_upwards with z
  rw [normalizedEval_zero_left]
  rw [show oneDimNormalization n 1 = Real.sqrt n by
    simp [oneDimNormalization]]
  simp [mul_assoc]

/-- Specialized noncompact complex Gaussian `dbar` integration by parts
for every normalized one-coordinate Hermite polynomial. -/
theorem complexGaussianDbarIntegrationByParts_normalizedEval
    (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    (∫ z : ℂ, dbarOnePublic (normalizedEval n hn p q) z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (n : ℂ) * ∫ z : ℂ, z * normalizedEval n hn p q z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (dbarOne_normalizedEval_public n hn p q))]
  rw [integral_const_mul, integral_normalizedEval_complexGaussian]
  have hs : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  apply mul_left_cancel₀ hs
  rw [show (Real.sqrt n : ℂ) * ((n : ℂ) *
      ∫ z : ℂ, z * normalizedEval n hn p q z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (n : ℂ) * ((Real.sqrt n : ℂ) *
        ∫ z : ℂ, z * normalizedEval n hn p q z
          ∂(complexCoordinateGaussianProbability n : Measure ℂ)) by ring,
    sqrt_mul_integral_coordinate_mul_normalizedEval n hn p q]
  by_cases hp : p = 0
  · subst p
    cases q with
    | zero => simp
    | succ q =>
      cases q with
      | zero =>
        simp only [zero_add, mul_one, tsub_self, and_self, ↓reduceIte]
        have hsq : Real.sqrt n * Real.sqrt n = n := by
          rw [Real.mul_self_sqrt (by positivity)]
        exact_mod_cast hsq
      | succ q => simp
  · simp [hp]

theorem conj_normalizedEval_swap (n : ℕ) (hn : 0 < n) (p q : ℕ) (z : ℂ) :
    conj (normalizedEval n hn p q z) = normalizedEval n hn q p z := by
  unfold normalizedEval normalized raw
  simp only [map_mul, map_sum, map_pow, map_natCast,
    MvPolynomial.eval_C]
  rw [min_comm]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Z, W, oneDimNormalization, mul_comm, mul_left_comm, mul_assoc]

theorem integrable_normalizedEval_mul_conj_normalizedEval
    (n : ℕ) (hn : 0 < n) (r s p q : ℕ) :
    Integrable (fun z : ℂ ↦ normalizedEval n hn r s z *
      conj (normalizedEval n hn p q z))
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [show (fun z : ℂ ↦ normalizedEval n hn r s z *
      conj (normalizedEval n hn p q z)) =
      fun z ↦ normalizedEval n hn r s z * normalizedEval n hn q p z by
    funext z
    rw [conj_normalizedEval_swap]]
  exact ComplexHermite.integrable_normalizedEval_mul n hn r s q p

theorem integrable_coordinate_mul_normalizedEval_mul_conj_normalizedEval
    (n : ℕ) (hn : 0 < n) (r s p q : ℕ) :
    Integrable (fun z : ℂ ↦ z * (normalizedEval n hn r s z *
      conj (normalizedEval n hn p q z)))
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  let P : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.X 0 * normalized n hn r s * normalized n hn q p
  have hP := integrable_mvPolynomial_diagonalEval n P
  apply hP.congr
  filter_upwards with z
  simp only [P, MvPolynomial.eval_mul, MvPolynomial.eval_X
    ]
  simp only [Matrix.cons_val_zero]
  change (z * normalizedEval n hn r s z) * normalizedEval n hn q p z = _
  rw [conj_normalizedEval_swap]
  ring

theorem complexGaussianDbarIntegrationByParts_normalizedEval_mul_conj
    (n : ℕ) (hn : 0 < n) (r s p q : ℕ) :
    (∫ z : ℂ, dbarOnePublic (fun w ↦ normalizedEval n hn r s w *
      conj (normalizedEval n hn p q w)) z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (n : ℂ) * ∫ z : ℂ, z * (normalizedEval n hn r s z *
        conj (normalizedEval n hn p q z))
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  let P : Poly := normalized n hn r s * normalized n hn q p
  have hfun : (fun z : ℂ ↦ normalizedEval n hn r s z *
      conj (normalizedEval n hn p q z)) = diagonalEvalPublic P := by
    funext z
    rw [conj_normalizedEval_swap]
    simp [P, diagonalEvalPublic, diagonalEval, normalizedEval, MvPolynomial.eval_mul]
  rw [hfun]
  rw [show (fun z : ℂ ↦ z * (normalizedEval n hn r s z *
      conj (normalizedEval n hn p q z))) =
      fun z ↦ z * diagonalEvalPublic P z by
    funext z
    rw [← congrFun hfun z]]
  exact complexGaussianDbarIntegrationByParts_diagonalEval hn P

theorem integral_normalizedEval_mul_conj_normalizedEval
    (n : ℕ) (hn : 0 < n) (r s p q : ℕ) :
    (∫ z : ℂ, normalizedEval n hn r s z *
      conj (normalizedEval n hn p q z)
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      if r = p ∧ s = q then 1 else 0 := by
  have h := normalizedEval_orthogonal_of_mixedMoments n hn
    (mixedMomentFormula_of_pos n hn) p q r s
  calc
    _ = ∫ z : ℂ, conj (normalizedEval n hn p q z) *
        normalizedEval n hn r s z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
          apply integral_congr_ae
          filter_upwards with z
          ring
    _ = if p = r ∧ q = s then 1 else 0 := h
    _ = if r = p ∧ s = q then 1 else 0 := by
      congr 1
      apply propext
      constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂.symm⟩

theorem dbarOnePublic_conj_normalizedEval
    (n : ℕ) (hn : 0 < n) (p q : ℕ) (z : ℂ) :
    dbarOnePublic (fun w ↦ conj (normalizedEval n hn p q w)) z =
      Real.sqrt (n * p : ℕ) * conj (normalizedEval n hn (p - 1) q z) := by
  rw [show (fun w ↦ conj (normalizedEval n hn p q w)) =
      normalizedEval n hn q p by funext w; exact conj_normalizedEval_swap n hn p q w]
  rw [dbarOne_normalizedEval_public]
  rw [conj_normalizedEval_swap]

theorem coordinate_normalizedEval_matrix_element
    (n : ℕ) (hn : 0 < n) (r s p q : ℕ) :
    (n : ℂ) * (∫ z : ℂ, z * (normalizedEval n hn r s z *
      conj (normalizedEval n hn p q z))
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (Real.sqrt (n * s : ℕ) : ℂ) *
          (if r = p ∧ s - 1 = q then 1 else 0) +
        (Real.sqrt (n * p : ℕ) : ℂ) *
          (if r = p - 1 ∧ s = q then 1 else 0) := by
  rw [← complexGaussianDbarIntegrationByParts_normalizedEval_mul_conj n hn r s p q]
  have hprod : (∫ z : ℂ, dbarOnePublic (fun w ↦
      normalizedEval n hn r s w * conj (normalizedEval n hn p q w)) z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      ∫ z : ℂ, dbarOnePublic (normalizedEval n hn r s) z *
          conj (normalizedEval n hn p q z) +
        normalizedEval n hn r s z *
          dbarOnePublic (fun w ↦ conj (normalizedEval n hn p q w)) z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
    apply integral_congr_ae
    filter_upwards with z
    exact dbarOnePublic_mul
      (differentiable_normalizedEval n hn r s)
      (Complex.differentiable_conj.comp
        (differentiable_normalizedEval n hn p q)) z
  rw [hprod]
  have hi1 : Integrable (fun z ↦ dbarOnePublic (normalizedEval n hn r s) z *
      conj (normalizedEval n hn p q z))
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
    ((integrable_normalizedEval_mul_conj_normalizedEval n hn
      r (s - 1) p q).const_mul (Real.sqrt (n * s : ℕ) : ℂ)).congr
      (Filter.Eventually.of_forall fun z ↦ by
        change (Real.sqrt (n * s : ℕ) : ℂ) *
            (normalizedEval n hn r (s - 1) z *
              conj (normalizedEval n hn p q z)) =
          dbarOnePublic (normalizedEval n hn r s) z *
            conj (normalizedEval n hn p q z)
        rw [dbarOne_normalizedEval_public]
        ring)
  have hi2 : Integrable (fun z ↦ normalizedEval n hn r s z *
      dbarOnePublic (fun w ↦ conj (normalizedEval n hn p q w)) z)
      (complexCoordinateGaussianProbability n : Measure ℂ) :=
    ((integrable_normalizedEval_mul_conj_normalizedEval n hn
      r s (p - 1) q).const_mul (Real.sqrt (n * p : ℕ) : ℂ)).congr
      (Filter.Eventually.of_forall fun z ↦ by
        change (Real.sqrt (n * p : ℕ) : ℂ) *
            (normalizedEval n hn r s z *
              conj (normalizedEval n hn (p - 1) q z)) =
          normalizedEval n hn r s z *
            dbarOnePublic (fun w ↦ conj (normalizedEval n hn p q w)) z
        rw [dbarOnePublic_conj_normalizedEval]
        ring)
  rw [integral_add hi1 hi2]
  have hInt1 : (∫ z : ℂ, dbarOnePublic (normalizedEval n hn r s) z *
      conj (normalizedEval n hn p q z)
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (Real.sqrt (n * s : ℕ) : ℂ) *
        (if r = p ∧ s - 1 = q then 1 else 0) := by
    calc
      _ = ∫ z : ℂ, (Real.sqrt (n * s : ℕ) : ℂ) *
          (normalizedEval n hn r (s - 1) z *
            conj (normalizedEval n hn p q z))
          ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
            apply integral_congr_ae
            filter_upwards with z
            rw [dbarOne_normalizedEval_public, mul_assoc]
      _ = _ := by rw [integral_const_mul,
        integral_normalizedEval_mul_conj_normalizedEval]
  have hInt2 : (∫ z : ℂ, normalizedEval n hn r s z *
      dbarOnePublic (fun w ↦ conj (normalizedEval n hn p q w)) z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (Real.sqrt (n * p : ℕ) : ℂ) *
        (if r = p - 1 ∧ s = q then 1 else 0) := by
    calc
      _ = ∫ z : ℂ, (Real.sqrt (n * p : ℕ) : ℂ) *
          (normalizedEval n hn r s z *
            conj (normalizedEval n hn (p - 1) q z))
          ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
            apply integral_congr_ae
            filter_upwards with z
            rw [dbarOnePublic_conj_normalizedEval, mul_left_comm]
      _ = _ := by rw [integral_const_mul,
        integral_normalizedEval_mul_conj_normalizedEval]
  rw [hInt1, hInt2]

theorem multivariate_coordinate_matrix_element_factorization
    (n : ℕ) (hn : 0 < n) (r s p q : Fin n → ℕ) (j : Fin n) :
    (∫ z : Configuration n, z j *
        (multivariateNormalized n hn r s z *
          conj (multivariateNormalized n hn p q z))
        ∂complexGaussianMeasure n) =
      (∫ z : ℂ, z * (normalizedEval n hn (r j) (s j) z *
          conj (normalizedEval n hn (p j) (q j) z))
          ∂(complexCoordinateGaussianProbability n : Measure ℂ)) *
        ∏ i ∈ Finset.univ.erase j,
          (∫ z : ℂ, normalizedEval n hn (r i) (s i) z *
            conj (normalizedEval n hn (p i) (q i) z)
            ∂(complexCoordinateGaussianProbability n : Measure ℂ)) := by
  unfold multivariateNormalized complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi, map_prod]
  let f : (i : Fin n) → ℂ → ℂ := fun i z ↦
    if i = j then z * (normalizedEval n hn (r i) (s i) z *
      conj (normalizedEval n hn (p i) (q i) z))
    else normalizedEval n hn (r i) (s i) z *
      conj (normalizedEval n hn (p i) (q i) z)
  have hfun : (fun z : Fin n → ℂ ↦ z j *
      ((∏ i, normalizedEval n hn (r i) (s i) (z i)) *
        (∏ i, conj (normalizedEval n hn (p i) (q i) (z i))))) =
      fun z ↦ ∏ i, f i (z i) := by
    funext z
    rw [← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton j _ (by simp)]
    rw [show (∏ i, f i (z i)) = f j (z j) *
        ∏ i ∈ Finset.univ \ {j}, f i (z i) by
      exact Finset.prod_eq_mul_prod_sdiff_singleton j _ (by intro h; simp at h)]
    simp only [f, ite_eq_left]
    ring_nf
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := by
      have := (Finset.mem_sdiff.mp hi).2
      simpa using this
    simp [hij]
  rw [hfun, integral_fintype_prod_eq_prod]
  have hsplit := Finset.prod_eq_mul_prod_sdiff_singleton
    (s := Finset.univ)
    (f := fun i ↦ ∫ z : ℂ, f i z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ))
    j (by simp)
  rw [hsplit]
  simp only [f, ite_eq_left]
  simp only [Finset.erase_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i ≠ j := by
    have := (Finset.mem_sdiff.mp hi).2
    simpa using this
  simp [hij]

theorem multivariate_coordinate_matrix_element
    (n : ℕ) (hn : 0 < n) (r s p q : Fin n → ℕ) (j : Fin n) :
    (n : ℂ) * (∫ z : Configuration n, z j *
        (multivariateNormalized n hn r s z *
          conj (multivariateNormalized n hn p q z))
        ∂complexGaussianMeasure n) =
      ((Real.sqrt (n * s j : ℕ) : ℂ) *
          (if r j = p j ∧ s j - 1 = q j then 1 else 0) +
        (Real.sqrt (n * p j : ℕ) : ℂ) *
          (if r j = p j - 1 ∧ s j = q j then 1 else 0)) *
        ∏ i ∈ Finset.univ.erase j,
          (if r i = p i ∧ s i = q i then (1 : ℂ) else 0) := by
  rw [multivariate_coordinate_matrix_element_factorization n hn r s p q j]
  rw [show (n : ℂ) *
      ((∫ z : ℂ, z * (normalizedEval n hn (r j) (s j) z *
        conj (normalizedEval n hn (p j) (q j) z))
        ∂(complexCoordinateGaussianProbability n : Measure ℂ)) *
        ∏ i ∈ Finset.univ.erase j,
          (∫ z : ℂ, normalizedEval n hn (r i) (s i) z *
            conj (normalizedEval n hn (p i) (q i) z)
            ∂(complexCoordinateGaussianProbability n : Measure ℂ))) =
      ((n : ℂ) * ∫ z : ℂ, z *
        (normalizedEval n hn (r j) (s j) z *
          conj (normalizedEval n hn (p j) (q j) z))
        ∂(complexCoordinateGaussianProbability n : Measure ℂ)) *
        ∏ i ∈ Finset.univ.erase j,
          (∫ z : ℂ, normalizedEval n hn (r i) (s i) z *
            conj (normalizedEval n hn (p i) (q i) z)
            ∂(complexCoordinateGaussianProbability n : Measure ℂ)) by ring]
  rw [coordinate_normalizedEval_matrix_element]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact integral_normalizedEval_mul_conj_normalizedEval n hn
    (r i) (s i) (p i) (q i)

theorem memLp_two_coordinate_mul_multivariateNormalized
    (n : ℕ) (hn : 0 < n) (p q : Fin n → ℕ) (j : Fin n) :
    MemLp (fun z : Configuration n ↦ z j *
      multivariateNormalized n hn p q z) 2 (complexGaussianMeasure n) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((continuous_apply j).mul
      (continuous_multivariateNormalized n hn p q)).aestronglyMeasurable).mpr
  change Integrable (fun z : Configuration n ↦
    ‖z j * multivariateNormalized n hn p q z‖ ^ 2) (complexGaussianMeasure n)
  rw [show (fun z : Configuration n ↦
      ‖z j * multivariateNormalized n hn p q z‖ ^ 2) =
      fun z ↦ ∏ i, if i = j then
        Complex.normSq (z i * normalizedEval n hn (p i) (q i) (z i))
      else Complex.normSq (normalizedEval n hn (p i) (q i) (z i)) by
    funext z
    unfold multivariateNormalized
    rw [norm_mul, norm_prod, mul_pow, ← Finset.prod_pow]
    rw [show (∏ i, ‖normalizedEval n hn (p i) (q i) (z i)‖ ^ 2) =
        ‖normalizedEval n hn (p j) (q j) (z j)‖ ^ 2 *
          ∏ i ∈ Finset.univ \ {j},
            ‖normalizedEval n hn (p i) (q i) (z i)‖ ^ 2 by
      exact Finset.prod_eq_mul_prod_sdiff_singleton j _ (by simp)]
    rw [show (∏ i, if i = j then
        Complex.normSq (z i * normalizedEval n hn (p i) (q i) (z i))
      else Complex.normSq (normalizedEval n hn (p i) (q i) (z i))) =
        Complex.normSq (z j * normalizedEval n hn (p j) (q j) (z j)) *
          ∏ i ∈ Finset.univ \ {j},
            (if i = j then Complex.normSq
              (z i * normalizedEval n hn (p i) (q i) (z i))
            else Complex.normSq (normalizedEval n hn (p i) (q i) (z i))) by
      simpa using Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
        (M := ℝ) (Finset.mem_univ j)
        (fun i : Fin n ↦ (if i = j then
          Complex.normSq (z i * normalizedEval n hn (p i) (q i) (z i))
        else Complex.normSq (normalizedEval n hn (p i) (q i) (z i))))]
    simp only [Complex.normSq_mul, Complex.sq_norm]
    ring_nf
    apply congrArg (fun w : ℝ ↦
      Complex.normSq (z j) *
        Complex.normSq (normalizedEval n hn (p j) (q j) (z j)) * w)
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := by
      have := (Finset.mem_sdiff.mp hi).2
      simpa using this
    simp [hij]]
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  refine Integrable.fintype_prod (μ := fun _ : Fin n ↦
    (complexCoordinateGaussianProbability n : Measure ℂ))
    (f := fun i w ↦ if i = j then Complex.normSq
      (w * normalizedEval n hn (p i) (q i) w)
    else Complex.normSq (normalizedEval n hn (p i) (q i) w)) ?_
  intro i
  by_cases hij : i = j
  · subst i
    simp only [ite_eq_left]
    let P : Poly := MvPolynomial.X 0 * MvPolynomial.X 1 *
      normalized n hn (p j) (q j) * normalized n hn (q j) (p j)
    exact (integrable_mvPolynomial_diagonalEval n P).re.congr
      (Filter.Eventually.of_forall fun z ↦ by
        change (MvPolynomial.eval ![z, conj z] P).re =
          Complex.normSq (z * normalizedEval n hn (p j) (q j) z)
        have hz : MvPolynomial.eval ![z, conj z] P =
            (Complex.normSq (z * normalizedEval n hn (p j) (q j) z) : ℂ) := by
          rw [Complex.normSq_eq_conj_mul_self]
          simp only [P, MvPolynomial.eval_X,
            Matrix.cons_val_zero, Matrix.cons_val_one, map_mul]
          rw [conj_normalizedEval_swap]
          change z * conj z * normalizedEval n hn (p j) (q j) z *
            normalizedEval n hn (q j) (p j) z = _
          ring
        rw [hz]
        simp)
  · simp only [ite_eq_right hij]
    exact ComplexHermite.integrable_normSq_normalizedEval n hn (p i) (q i)

/-- The Gaussian L² class of a normalized multivariate Hermite function times one coordinate. -/
def coordinateMulMultivariateNormalizedL2
    (n : ℕ) (hn : 0 < n) (p q : Fin n → ℕ) (j : Fin n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  (memLp_two_coordinate_mul_multivariateNormalized n hn p q j).toLp
    (fun z ↦ z j * multivariateNormalized n hn p q z)

theorem coordinateMulMultivariateNormalizedL2_coeFn
    (n : ℕ) (hn : 0 < n) (p q : Fin n → ℕ) (j : Fin n) :
    coordinateMulMultivariateNormalizedL2 n hn p q j =ᵐ[complexGaussianMeasure n]
      fun z ↦ z j * multivariateNormalized n hn p q z :=
  MemLp.coeFn_toLp (memLp_two_coordinate_mul_multivariateNormalized n hn p q j)

theorem gaussianHermiteCoefficient_coordinateMulMultivariateNormalizedL2
    (n : ℕ) (hn : 0 < n) (r s p q : Fin n → ℕ) (j : Fin n) :
    (n : ℂ) * gaussianHermiteCoefficient hn
        (coordinateMulMultivariateNormalizedL2 n hn r s j) (p, q) =
      ((Real.sqrt (n * s j : ℕ) : ℂ) *
          (if r j = p j ∧ s j - 1 = q j then 1 else 0) +
        (Real.sqrt (n * p j : ℕ) : ℂ) *
          (if r j = p j - 1 ∧ s j = q j then 1 else 0)) *
        ∏ i ∈ Finset.univ.erase j,
          (if r i = p i ∧ s i = q i then (1 : ℂ) else 0) := by
  rw [gaussianHermiteCoefficient_eq_inner]
  have hi : inner ℂ (multivariateNormalizedL2 n hn p q)
      (coordinateMulMultivariateNormalizedL2 n hn r s j) =
      ∫ z : Configuration n, z j *
        (multivariateNormalized n hn r s z *
          conj (multivariateNormalized n hn p q z))
        ∂complexGaussianMeasure n := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [multivariateNormalizedL2_coeFn n hn p q,
      coordinateMulMultivariateNormalizedL2_coeFn n hn r s j] with z hp hz
    rw [RCLike.inner_apply, hp, hz]
    ring
  rw [hi]
  exact multivariate_coordinate_matrix_element n hn r s p q j

private theorem eq_iff_eq_at_and_eq_off {n : ℕ} (a b : Fin n → ℕ)
    (j : Fin n) :
    a = b ↔ a j = b j ∧ ∀ i ∈ Finset.univ.erase j, a i = b i := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ ↦ rfl⟩
  · rintro ⟨hj, hoff⟩
    funext i
    by_cases hij : i = j
    · simpa [hij] using hj
    · exact hoff i (by simp [hij])

private theorem lower_local_off_iff {n : ℕ} (r s p q : Fin n → ℕ)
    (j : Fin n) (_hs : 0 < s j) :
    ((r j = p j ∧ s j - 1 = q j) ∧
        ∀ i ∈ Finset.univ.erase j, r i = p i ∧ s i = q i) ↔
      (p, q) = (r, lowerAt s j) := by
  rw [Prod.ext_iff]
  constructor
  · rintro ⟨hlocal, hoff⟩
    constructor
    · rw [eq_iff_eq_at_and_eq_off]
      exact ⟨hlocal.1.symm, fun i hi ↦ (hoff i hi).1.symm⟩
    · rw [eq_iff_eq_at_and_eq_off]
      constructor
      · change q j = lowerAt s j j
        simpa [lowerAt] using hlocal.2.symm
      · intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        simpa [lowerAt, Function.update_of_ne hij] using (hoff i hi).2.symm
  · rintro ⟨hp, hq⟩
    constructor
    · constructor
      · exact (congrFun hp j).symm
      · simpa [lowerAt] using (congrFun hq j).symm
    · intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      exact ⟨(congrFun hp i).symm,
        by simpa [lowerAt, Function.update_of_ne hij] using (congrFun hq i).symm⟩

private theorem raise_local_off_iff {n : ℕ} (r s p q : Fin n → ℕ)
    (j : Fin n) (hpj : 0 < p j) :
    ((r j = p j - 1 ∧ s j = q j) ∧
        ∀ i ∈ Finset.univ.erase j, r i = p i ∧ s i = q i) ↔
      (p, q) = (raiseAt r j, s) := by
  rw [Prod.ext_iff]
  constructor
  · rintro ⟨hlocal, hoff⟩
    have hpjr : p j = r j + 1 := by omega
    constructor
    · rw [eq_iff_eq_at_and_eq_off]
      constructor
      · change p j = raiseAt r j j
        simpa [raiseAt] using hpjr
      · intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        simpa [raiseAt, Function.update_of_ne hij] using (hoff i hi).1.symm
    · rw [eq_iff_eq_at_and_eq_off]
      exact ⟨hlocal.2.symm, fun i hi ↦ (hoff i hi).2.symm⟩
  · rintro ⟨hp, hq⟩
    constructor
    · constructor
      · have hj := congrFun hp j
        simp [raiseAt] at hj
        omega
      · exact (congrFun hq j).symm
    · intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      exact ⟨by simpa [raiseAt, Function.update_of_ne hij] using (congrFun hp i).symm,
        (congrFun hq i).symm⟩

private theorem prod_indicator_eq_ite {α : Type*}
    (t : Finset α) (P : α → Prop) [DecidablePred P] :
    (∏ i ∈ t, (if P i then (1 : ℂ) else 0)) =
      if ∀ i ∈ t, P i then 1 else 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
      simp only [Finset.prod_insert hat, ih, Finset.mem_insert]
      by_cases ha : P a <;> by_cases ht : ∀ i ∈ t, P i <;> simp [ha, ht]

private theorem lower_scalar_indicator {n : ℕ} (r s p q : Fin n → ℕ)
    (j : Fin n) :
    (Real.sqrt (n * s j : ℕ) : ℂ) *
        (if r j = p j ∧ s j - 1 = q j then 1 else 0) *
        ∏ i ∈ Finset.univ.erase j,
          (if r i = p i ∧ s i = q i then (1 : ℂ) else 0) =
      (Real.sqrt (n * s j : ℕ) : ℂ) *
        (if (p, q) = (r, lowerAt s j) then 1 else 0) := by
  classical
  rw [prod_indicator_eq_ite]
  by_cases hs : s j = 0
  · simp [hs]
  · have hspos := Nat.pos_of_ne_zero hs
    let A := r j = p j ∧ s j - 1 = q j
    let O := ∀ i ∈ Finset.univ.erase j, r i = p i ∧ s i = q i
    have hiff := lower_local_off_iff r s p q j hspos
    by_cases hpair : (p, q) = (r, lowerAt s j)
    · have hAO := hiff.mpr hpair
      rw [ite_eq_left hpair, ite_eq_left hAO.1, ite_eq_left hAO.2]
      ring
    · have hnAO : ¬(A ∧ O) := by
        intro h
        exact hpair (hiff.mp h)
      rw [ite_eq_right hpair]
      by_cases hA : A
      · by_cases hO : O
        · exact (hnAO ⟨hA, hO⟩).elim
        · change ¬∀ i ∈ Finset.univ.erase j,
              r i = p i ∧ s i = q i at hO
          rw [ite_eq_left hA, ite_eq_right hO]
          simp
      · change ¬(r j = p j ∧ s j - 1 = q j) at hA
        rw [ite_eq_right hA]
        simp

private theorem raise_scalar_indicator {n : ℕ} (r s p q : Fin n → ℕ)
    (j : Fin n) :
    (Real.sqrt (n * p j : ℕ) : ℂ) *
        (if r j = p j - 1 ∧ s j = q j then 1 else 0) *
        ∏ i ∈ Finset.univ.erase j,
          (if r i = p i ∧ s i = q i then (1 : ℂ) else 0) =
      (Real.sqrt (n * (r j + 1) : ℕ) : ℂ) *
        (if (p, q) = (raiseAt r j, s) then 1 else 0) := by
  classical
  rw [prod_indicator_eq_ite]
  by_cases hp : p j = 0
  · have hne : (p, q) ≠ (raiseAt r j, s) := by
      intro h
      have hj := congrFun (congrArg Prod.fst h) j
      simp [raiseAt, hp] at hj
    simp [hp, hne]
  · have hppos := Nat.pos_of_ne_zero hp
    let B := r j = p j - 1 ∧ s j = q j
    let O := ∀ i ∈ Finset.univ.erase j, r i = p i ∧ s i = q i
    have hiff := raise_local_off_iff r s p q j hppos
    by_cases hpair : (p, q) = (raiseAt r j, s)
    · have hBO := hiff.mpr hpair
      have heq : p j = r j + 1 := by
        change (r j = p j - 1 ∧ s j = q j) ∧ _ at hBO
        omega
      rw [ite_eq_left hpair, ite_eq_left hBO.1, ite_eq_left hBO.2, heq]
      ring
    · have hnBO : ¬(B ∧ O) := by
        intro h
        exact hpair (hiff.mp h)
      rw [ite_eq_right hpair]
      by_cases hB : B
      · by_cases hO : O
        · exact (hnBO ⟨hB, hO⟩).elim
        · change ¬∀ i ∈ Finset.univ.erase j,
              r i = p i ∧ s i = q i at hO
          rw [ite_eq_left hB, ite_eq_right hO]
          simp
      · change ¬(r j = p j - 1 ∧ s j = q j) at hB
        rw [ite_eq_right hB]
        simp

theorem gaussianHermiteCoefficient_coordinateMul_creation_form
    (n : ℕ) (hn : 0 < n) (r s p q : Fin n → ℕ) (j : Fin n) :
    (n : ℂ) * gaussianHermiteCoefficient hn
        (coordinateMulMultivariateNormalizedL2 n hn r s j) (p, q) =
      (Real.sqrt (n * s j : ℕ) : ℂ) *
          (if (p, q) = (r, lowerAt s j) then 1 else 0) +
        (Real.sqrt (n * (r j + 1) : ℕ) : ℂ) *
          (if (p, q) = (raiseAt r j, s) then 1 else 0) := by
  rw [gaussianHermiteCoefficient_coordinateMulMultivariateNormalizedL2]
  rw [add_mul, lower_scalar_indicator, raise_scalar_indicator]

theorem coordinateMulMultivariateNormalizedL2_creation
    (n : ℕ) (hn : 0 < n) (r s : Fin n → ℕ) (j : Fin n) :
    (n : ℂ) • coordinateMulMultivariateNormalizedL2 n hn r s j =
      (Real.sqrt (n * s j : ℕ) : ℂ) •
          multivariateNormalizedL2 n hn r (lowerAt s j) +
        (Real.sqrt (n * (r j + 1) : ℕ) : ℂ) •
          multivariateNormalizedL2 n hn (raiseAt r j) s := by
  apply (gaussianHermiteHilbertBasis n hn).repr.injective
  ext pq
  change gaussianHermiteCoefficient hn
      ((n : ℂ) • coordinateMulMultivariateNormalizedL2 n hn r s j) pq =
    gaussianHermiteCoefficient hn
      ((Real.sqrt (n * s j : ℕ) : ℂ) •
          multivariateNormalizedL2 n hn r (lowerAt s j) +
        (Real.sqrt (n * (r j + 1) : ℕ) : ℂ) •
          multivariateNormalizedL2 n hn (raiseAt r j) s) pq
  simp only [gaussianHermiteCoefficient, map_smul, map_add
    ]
  change (n : ℂ) * gaussianHermiteCoefficient hn
      (coordinateMulMultivariateNormalizedL2 n hn r s j) pq = _
  rw [gaussianHermiteCoefficient_coordinateMul_creation_form]
  change _ = (Real.sqrt (n * s j : ℕ) : ℂ) *
      (gaussianHermiteHilbertBasis n hn).repr
        (multivariateNormalizedL2 n hn r (lowerAt s j)) pq +
    (Real.sqrt (n * (r j + 1) : ℕ) : ℂ) *
      (gaussianHermiteHilbertBasis n hn).repr
        (multivariateNormalizedL2 n hn (raiseAt r j) s) pq
  have h₁ : (gaussianHermiteHilbertBasis n hn).repr
      (multivariateNormalizedL2 n hn r (lowerAt s j)) pq =
        if pq = (r, lowerAt s j) then 1 else 0 := by
    rw [← gaussianHermiteCoefficient, gaussianHermiteCoefficient_eq_inner]
    simpa [multivariateNormalizedL2, hermiteL2Family] using
      inner_hermiteL2Family n hn (mixedMomentFormula_of_pos n hn) pq
        (r, lowerAt s j)
  have h₂ : (gaussianHermiteHilbertBasis n hn).repr
      (multivariateNormalizedL2 n hn (raiseAt r j) s) pq =
        if pq = (raiseAt r j, s) then 1 else 0 := by
    rw [← gaussianHermiteCoefficient, gaussianHermiteCoefficient_eq_inner]
    simpa [multivariateNormalizedL2, hermiteL2Family] using
      inner_hermiteL2Family n hn (mixedMomentFormula_of_pos n hn) pq
        (raiseAt r j, s)
  rw [h₁, h₂]

theorem coordinate_mul_multivariateNormalized_creation_ae
    (n : ℕ) (hn : 0 < n) (r s : Fin n → ℕ) (j : Fin n) :
    (fun z : Configuration n ↦ (n : ℂ) * z j *
        multivariateNormalized n hn r s z) =ᵐ[complexGaussianMeasure n]
      fun z ↦ (Real.sqrt (n * s j : ℕ) : ℂ) *
          multivariateNormalized n hn r (lowerAt s j) z +
        (Real.sqrt (n * (r j + 1) : ℕ) : ℂ) *
          multivariateNormalized n hn (raiseAt r j) s z := by
  have hv := coordinateMulMultivariateNormalizedL2_creation n hn r s j
  have hvfun := congrArg
    (fun x : Lp ℂ 2 (complexGaussianMeasure n) ↦
      (x : Configuration n → ℂ)) hv
  have hve : ∀ᵐ z ∂complexGaussianMeasure n,
      ((↑((n : ℂ) • coordinateMulMultivariateNormalizedL2 n hn r s j) :
          Configuration n → ℂ) z) =
        ((↑((Real.sqrt (n * s j : ℕ) : ℂ) •
            multivariateNormalizedL2 n hn r (lowerAt s j) +
          (Real.sqrt (n * (r j + 1) : ℕ) : ℂ) •
            multivariateNormalizedL2 n hn (raiseAt r j) s) :
              Configuration n → ℂ) z) :=
    Filter.Eventually.of_forall fun z ↦ congrFun hvfun z
  filter_upwards [hve,
    MeasureTheory.Lp.coeFn_smul (n : ℂ)
      (coordinateMulMultivariateNormalizedL2 n hn r s j),
    MeasureTheory.Lp.coeFn_add
      ((Real.sqrt (n * s j : ℕ) : ℂ) •
        multivariateNormalizedL2 n hn r (lowerAt s j))
      ((Real.sqrt (n * (r j + 1) : ℕ) : ℂ) •
        multivariateNormalizedL2 n hn (raiseAt r j) s),
    MeasureTheory.Lp.coeFn_smul (Real.sqrt (n * s j : ℕ) : ℂ)
      (multivariateNormalizedL2 n hn r (lowerAt s j)),
    MeasureTheory.Lp.coeFn_smul (Real.sqrt (n * (r j + 1) : ℕ) : ℂ)
      (multivariateNormalizedL2 n hn (raiseAt r j) s),
    coordinateMulMultivariateNormalizedL2_coeFn n hn r s j,
    multivariateNormalizedL2_coeFn n hn r (lowerAt s j),
    multivariateNormalizedL2_coeFn n hn (raiseAt r j) s] with
      z hz hns hadd hslo hsra hcoord hlo hra
  calc
    (n : ℂ) * z j * multivariateNormalized n hn r s z =
        ((n : ℂ) • (coordinateMulMultivariateNormalizedL2 n hn r s j :
          Configuration n → ℂ)) z := by
      rw [Pi.smul_apply, hcoord]
      simp only [smul_eq_mul, mul_assoc]
    _ = ((↑((n : ℂ) • coordinateMulMultivariateNormalizedL2 n hn r s j) :
          Configuration n → ℂ) z) := hns.symm
    _ = _ := hz
    _ = ((↑((Real.sqrt (n * s j : ℕ) : ℂ) •
          multivariateNormalizedL2 n hn r (lowerAt s j)) :
            Configuration n → ℂ) +
        ↑((Real.sqrt (n * (r j + 1) : ℕ) : ℂ) •
          multivariateNormalizedL2 n hn (raiseAt r j) s)) z := hadd
    _ = _ := by rw [Pi.add_apply, hslo, hsra, Pi.smul_apply,
      Pi.smul_apply, hlo, hra]; rfl

theorem contDiff_normalizedEval_real (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    ContDiff ℝ 1 (normalizedEval n hn p q) := by
  exact contDiff_diagonalEval_public (normalized n hn p q)

theorem contDiff_multivariateNormalized_real (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    ContDiff ℝ 1 (multivariateNormalized n hn p q) := by
  unfold multivariateNormalized
  let f : Fin n → Configuration n → ℂ :=
    fun i z ↦ normalizedEval n hn (p i) (q i) (z i)
  have hf : ∀ i, ContDiff ℝ 1 (f i) := fun i ↦
    (contDiff_normalizedEval_real n hn (p i) (q i)).comp
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff
  change ContDiff ℝ 1 (fun z ↦ ∏ i ∈ Finset.univ, f i z)
  exact contDiff_prod fun i _ => hf i

theorem C_mul_Z_pow_mul_W_pow_eq_monomial (c : ℂ) (a b : ℕ) :
    MvPolynomial.C c * Z ^ a * W ^ b =
      MvPolynomial.monomial
        (Finsupp.single 0 a + Finsupp.single 1 b) c := by
  rw [show MvPolynomial.C c * Z ^ a =
      MvPolynomial.monomial (Finsupp.single 0 a) c by
    exact MvPolynomial.C_mul_X_pow_eq_monomial]
  rw [show W ^ b = MvPolynomial.monomial (Finsupp.single 1 b) 1 by
    exact MvPolynomial.X_pow_eq_monomial]
  rw [MvPolynomial.monomial_mul_monomial, mul_one]

theorem coeff_raw (ρ : ℝ) (p q : ℕ) (d : ComplexHermiteIndex →₀ ℕ) :
    (raw ρ p q).coeff d =
      ∑ k ∈ Finset.range (min p q + 1),
        if d = Finsupp.single 0 (p - k) + Finsupp.single 1 (q - k) then
          ((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) *
            (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ) else 0 := by
  unfold raw
  simp_rw [show ∀ k : ℕ,
      MvPolynomial.C (((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) *
        (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
        Z ^ (p - k) * W ^ (q - k) =
      MvPolynomial.monomial
        (Finsupp.single 0 (p - k) + Finsupp.single 1 (q - k))
        (((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) *
          (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) by
    intro k
    exact C_mul_Z_pow_mul_W_pow_eq_monomial _ _ _]
  simp [eq_comm]

theorem hermiteExponent_injective_of_le {p q k l : ℕ}
    (hk : k ≤ p) (hl : l ≤ p)
    (h : Finsupp.single (0 : ComplexHermiteIndex) (p - k) +
        Finsupp.single 1 (q - k) =
      Finsupp.single 0 (p - l) + Finsupp.single 1 (q - l)) :
    k = l := by
  have h0 := congrArg (fun d : ComplexHermiteIndex →₀ ℕ ↦ d 0) h
  have hsub : p - k = p - l := by
    simpa [Finsupp.single_apply] using h0
  omega

theorem hermiteExponent_injective_on_range {p q k l : ℕ}
    (hk : k ∈ Finset.range (min p q + 1))
    (hl : l ∈ Finset.range (min p q + 1))
    (h : Finsupp.single (0 : ComplexHermiteIndex) (p - k) +
        Finsupp.single 1 (q - k) =
      Finsupp.single 0 (p - l) + Finsupp.single 1 (q - l)) :
    k = l := by
  apply hermiteExponent_injective_of_le
  · exact (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans (min_le_left p q)
  · exact (Nat.le_of_lt_succ (Finset.mem_range.mp hl)).trans (min_le_left p q)
  · exact h

theorem coeff_raw_eq_of_exponent {ρ : ℝ} {p q k : ℕ}
    (hk : k ∈ Finset.range (min p q + 1)) :
    (raw ρ p q).coeff
        (Finsupp.single 0 (p - k) + Finsupp.single 1 (q - k)) =
      ((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) *
        (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ) := by
  rw [coeff_raw]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l hl hlk
    simp only [ite_eq_right_iff]
    intro he
    exact (hlk (hermiteExponent_injective_on_range hl hk he.symm)).elim
  · exact fun hkn => (hkn hk).elim

theorem coeff_raw_eq_zero_of_no_exponent {ρ : ℝ} {p q : ℕ}
    {d : ComplexHermiteIndex →₀ ℕ}
    (hd : ∀ k ∈ Finset.range (min p q + 1),
      d ≠ Finsupp.single 0 (p - k) + Finsupp.single 1 (q - k)) :
    (raw ρ p q).coeff d = 0 := by
  rw [coeff_raw]
  apply Finset.sum_eq_zero
  intro k hk
  split_ifs with h
  · exact (hd k hk h).elim
  · rfl

theorem raw_creation_scalar_identity (ρ : ℝ) (p q l : ℕ) :
    ((-(ρ : ℂ)) ^ (l + 1)) * ((l + 1).factorial : ℂ) *
          (Nat.choose (p + 1) (l + 1) : ℂ) * (Nat.choose q (l + 1) : ℂ) +
      (ρ : ℂ) * (q : ℂ) *
        (((-(ρ : ℂ)) ^ l) * (l.factorial : ℂ) *
          (Nat.choose p l : ℂ) * (Nat.choose (q - 1) l : ℂ)) =
    ((-(ρ : ℂ)) ^ (l + 1)) * ((l + 1).factorial : ℂ) *
      (Nat.choose p (l + 1) : ℂ) * (Nat.choose q (l + 1) : ℂ) := by
  cases q with
  | zero => simp
  | succ q =>
      rw [Nat.succ_sub_one, Nat.choose_succ_succ, Nat.factorial_succ]
      have hchooseNat := Nat.add_one_mul_choose_eq q l
      have hchoose : ((q + 1 : ℕ) : ℂ) * (Nat.choose q l : ℂ) =
          (Nat.choose (q + 1) (l + 1) : ℂ) * ((l + 1 : ℕ) : ℂ) := by
        exact_mod_cast hchooseNat
      push_cast
      simp only [Nat.succ_eq_add_one]
      rw [pow_succ]
      ring_nf
      push_cast at hchoose
      ring_nf at hchoose
      linear_combination
        ((ρ : ℂ) * (ρ : ℂ) ^ l * (l.factorial : ℂ) *
          (Nat.choose p l : ℂ) * (-1 : ℂ) ^ l) * hchoose

theorem conj_multivariateNormalized_swap (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (z : Configuration n) :
    conj (multivariateNormalized n hn p q z) =
      multivariateNormalized n hn q p z := by
  unfold multivariateNormalized
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact conj_normalizedEval_swap n hn (p i) (q i) (z i)

theorem dbarComponent_conj_multivariateNormalized (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (j : Fin n) (z : Configuration n) :
    dbarComponent (fun w ↦ conj (multivariateNormalized n hn p q w)) j z =
      Real.sqrt (n * p j : ℕ) *
        multivariateNormalized n hn q (lowerAt p j) z := by
  rw [show (fun w ↦ conj (multivariateNormalized n hn p q w)) =
      multivariateNormalized n hn q p by
    funext w
    exact conj_multivariateNormalized_swap n hn p q w]
  exact dbarComponent_multivariateNormalized n hn q p j z

theorem continuous_dbarComponent {n : ℕ} {F : Configuration n → ℂ}
    (hF : ContDiff ℝ 1 F) (j : Fin n) :
    Continuous (dbarComponent F j) := by
  unfold dbarComponent
  exact continuous_const.mul
    (((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
      (continuous_const.mul
        ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

theorem hasCompactSupport_dbarComponent {n : ℕ} {F : Configuration n → ℂ}
    (hFc : HasCompactSupport F) (j : Fin n) :
    HasCompactSupport (dbarComponent F j) := by
  unfold dbarComponent
  exact ((hFc.fderiv_apply ℝ (realCoordinateDirection j)).add
    ((hFc.fderiv_apply ℝ (imaginaryCoordinateDirection j)).mul_left)).mul_left

theorem memLp_dbarComponent {n : ℕ} {F : Configuration n → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (j : Fin n) :
    MemLp (dbarComponent F j) 2 (complexGaussianMeasure n) :=
  (continuous_dbarComponent hF j).memLp_of_hasCompactSupport
    (hasCompactSupport_dbarComponent hFc j)

/-- The Gaussian `L²` vector represented by a compactly supported smooth
coordinate `dbar` derivative. -/
def smoothDbarComponentL2 {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (j : Fin n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  (memLp_dbarComponent hF hFc j).toLp (dbarComponent F j)

theorem smoothDbarComponentL2_coeFn {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (j : Fin n) :
    smoothDbarComponentL2 F hF hFc j =ᵐ[complexGaussianMeasure n]
      dbarComponent F j :=
  MemLp.coeFn_toLp (memLp_dbarComponent hF hFc j)

/-- A compactly supported smooth function, regarded as a Gaussian `L²`
vector. -/
def smoothCompactL2 {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  hF.continuous.memLp_of_hasCompactSupport hFc |>.toLp F

theorem smoothCompactL2_coeFn {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    smoothCompactL2 F hF hFc =ᵐ[complexGaussianMeasure n] F :=
  MemLp.coeFn_toLp (hF.continuous.memLp_of_hasCompactSupport hFc)

theorem gaussianHermiteCoefficient_smoothCompactL2_eq_integral
    {n : ℕ} (hn : 0 < n) (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (smoothCompactL2 F hF hFc) pq =
      ∫ z, conj (multivariateNormalized n hn pq.1 pq.2 z) * F z
        ∂complexGaussianMeasure n := by
  rw [gaussianHermiteCoefficient_eq_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multivariateNormalizedL2_coeFn n hn pq.1 pq.2,
    smoothCompactL2_coeFn F hF hFc] with z hH hG
  rw [RCLike.inner_apply, hH, hG]
  ring

theorem gaussianHermiteCoefficient_smoothDbarComponentL2_eq_integral
    {n : ℕ} (hn : 0 < n) (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (j : Fin n)
    (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (smoothDbarComponentL2 F hF hFc j) pq =
      ∫ z, conj (multivariateNormalized n hn pq.1 pq.2 z) *
        dbarComponent F j z ∂complexGaussianMeasure n := by
  rw [gaussianHermiteCoefficient_eq_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multivariateNormalizedL2_coeFn n hn pq.1 pq.2,
    smoothDbarComponentL2_coeFn F hF hFc j] with z hH hD
  rw [RCLike.inner_apply, hH, hD]
  ring

/-- Gaussian integration by parts realizes `dbar` as the Hermite lowering
operator on every compactly supported smooth function. -/
theorem gaussianHermiteCoefficient_smoothDbarComponentL2_raise
    {n : ℕ} (hn : 0 < n) (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (j : Fin n)
    (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (smoothDbarComponentL2 F hF hFc j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn (smoothCompactL2 F hF hFc)
          (raiseHermiteIndex j pq) := by
  let H : Configuration n → ℂ :=
    fun z => multivariateNormalized n hn pq.1 pq.2 z
  have hH : ContDiff ℝ 1 H := contDiff_multivariateNormalized_real n hn _ _
  have hconjH : ContDiff ℝ 1 (fun z => conj (H z)) :=
    Complex.conjCLE.contDiff.comp hH
  have hprod : ContDiff ℝ 1 (fun z => F z * conj (H z)) := hF.mul hconjH
  have hcprod : HasCompactSupport (fun z => F z * conj (H z)) := hFc.mul_right
  have hibp := configurationGaussianDbarIntegrationByParts hn j hprod hcprod
  have hiD : Integrable (fun z => conj (H z) * dbarComponent F j z)
      (complexGaussianMeasure n) :=
    (hconjH.continuous.mul (continuous_dbarComponent hF j)).integrable_of_hasCompactSupport
      (hasCompactSupport_dbarComponent hFc j).mul_left
  have hiL : Integrable (fun z => F z *
      ((Real.sqrt (n * pq.1 j : ℕ) : ℂ) *
        multivariateNormalized n hn pq.2 (lowerAt pq.1 j) z))
      (complexGaussianMeasure n) :=
    (hF.continuous.mul
      (continuous_const.mul
        (continuous_multivariateNormalized n hn _ _))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hleft : (∫ z, dbarComponent (fun w => F w * conj (H w)) j z
      ∂complexGaussianMeasure n) =
      (∫ z, F z * ((Real.sqrt (n * pq.1 j : ℕ) : ℂ) *
        multivariateNormalized n hn pq.2 (lowerAt pq.1 j) z)
        ∂complexGaussianMeasure n) +
      ∫ z, conj (H z) * dbarComponent F j z
        ∂complexGaussianMeasure n := by
    rw [← integral_add hiL hiD]
    apply integral_congr_ae
    filter_upwards with z
    rw [dbarComponent_mul (hF.differentiable (by norm_num))
        (hconjH.differentiable (by norm_num)),
      dbarComponent_conj_multivariateNormalized n hn]
    ring
  have hright : (n : ℂ) * (∫ z, z j * (F z * conj (H z))
      ∂complexGaussianMeasure n) =
      (∫ z, F z * ((Real.sqrt (n * pq.1 j : ℕ) : ℂ) *
        multivariateNormalized n hn pq.2 (lowerAt pq.1 j) z)
        ∂complexGaussianMeasure n) +
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        ∫ z, multivariateNormalized n hn
          (raiseAt pq.2 j) pq.1 z * F z ∂complexGaussianMeasure n := by
    rw [← integral_const_mul]
    have hae := coordinate_mul_multivariateNormalized_creation_ae
      n hn pq.2 pq.1 j
    have hae' : (fun z => (n : ℂ) * (z j * (F z * conj (H z))))
        =ᵐ[complexGaussianMeasure n]
        (fun z => F z * ((Real.sqrt (n * pq.1 j : ℕ) : ℂ) *
            multivariateNormalized n hn pq.2 (lowerAt pq.1 j) z)) +
          fun z => (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
            (multivariateNormalized n hn (raiseAt pq.2 j) pq.1 z * F z) := by
      filter_upwards [hae] with z hz
      dsimp [H]
      rw [conj_multivariateNormalized_swap]
      calc
        (n : ℂ) * (z j * (F z *
            multivariateNormalized n hn pq.2 pq.1 z)) =
            F z * ((n : ℂ) * z j *
              multivariateNormalized n hn pq.2 pq.1 z) := by ring
        _ = _ := by rw [hz]; ring
    have hiR : Integrable (fun z =>
        (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
          (multivariateNormalized n hn (raiseAt pq.2 j) pq.1 z * F z))
        (complexGaussianMeasure n) := by
      apply Integrable.const_mul
      exact (continuous_multivariateNormalized n hn _ _).mul hF.continuous
          |>.integrable_of_hasCompactSupport hFc.mul_left
    rw [integral_congr_ae hae']
    simp only [Pi.add_apply]
    rw [integral_add hiL hiR, integral_const_mul]
  rw [gaussianHermiteCoefficient_smoothDbarComponentL2_eq_integral,
    gaussianHermiteCoefficient_smoothCompactL2_eq_integral]
  dsimp only [raiseHermiteIndex]
  have htarget :
      (∫ z, conj (multivariateNormalized n hn pq.1 (raiseAt pq.2 j) z) * F z
        ∂complexGaussianMeasure n) =
      ∫ z, multivariateNormalized n hn (raiseAt pq.2 j) pq.1 z * F z
        ∂complexGaussianMeasure n := by
    apply integral_congr_ae
    filter_upwards with z
    rw [conj_multivariateNormalized_swap]
  rw [htarget]
  have hsource :
      (∫ z, conj (multivariateNormalized n hn pq.1 pq.2 z) *
        dbarComponent F j z ∂complexGaussianMeasure n) =
      ∫ z, conj (H z) * dbarComponent F j z
        ∂complexGaussianMeasure n := by rfl
  rw [hsource]
  rw [hleft] at hibp
  rw [hright] at hibp
  exact add_left_cancel hibp

theorem norm_sq_smoothDbarComponentL2 {n : ℕ}
    (F : Configuration n → ℂ) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (j : Fin n) :
    ‖smoothDbarComponentL2 F hF hFc j‖ ^ 2 =
      ∫ z, Complex.normSq (dbarComponent F j z)
        ∂complexGaussianMeasure n := by
  have hinner : inner ℂ (smoothDbarComponentL2 F hF hFc j)
      (smoothDbarComponentL2 F hF hFc j) =
      ∫ z, inner ℂ ((smoothDbarComponentL2 F hF hFc j) z)
        ((smoothDbarComponentL2 F hF hFc j) z)
        ∂complexGaussianMeasure n :=
    MeasureTheory.L2.inner_def _ _
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hc := smoothDbarComponentL2_coeFn F hF hFc j
  rw [integral_congr_ae (by filter_upwards [hc] with z hz; rw [hz])] at hinner
  have hi : (fun z => inner ℂ (dbarComponent F j z) (dbarComponent F j z)) =
      fun z => (Complex.normSq (dbarComponent F j z) : ℂ) := by
    funext z
    rw [inner_self_eq_norm_sq_to_K]
    calc
      (‖dbarComponent F j z‖ : ℂ) ^ 2 =
          ((‖dbarComponent F j z‖ ^ 2 : ℝ) : ℂ) := by norm_cast
      _ = _ := congrArg Complex.ofReal (Complex.sq_norm (dbarComponent F j z))
  rw [hi, integral_complex_ofReal] at hinner
  apply Complex.ofReal_injective
  push_cast
  exact hinner

theorem sum_norm_sq_smoothDbarComponentL2 {n : ℕ} (_hn : 0 < n)
    (F : Configuration n → ℂ) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) :
    (1 / n : ℝ) * ∑ j : Fin n, ‖smoothDbarComponentL2 F hF hFc j‖ ^ 2 =
      gaussianDbarEnergy n F := by
  unfold gaussianDbarEnergy dbarNormSq
  congr 1
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact norm_sq_smoothDbarComponentL2 F hF hFc j
  · intro j _
    exact (Complex.continuous_normSq.comp (continuous_dbarComponent hF j))
      |>.integrable_of_hasCompactSupport
        ((hasCompactSupport_dbarComponent hFc j).comp_left (by simp))

theorem smoothDbarComponent_modeParseval {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℂ) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (j : Fin n) :
    ∑' d, ‖gaussianHermiteMode hn d (smoothDbarComponentL2 F hF hFc j)‖ ^ 2 =
      ‖smoothDbarComponentL2 F hF hFc j‖ ^ 2 :=
  tsum_norm_sq_gaussianHermiteMode hn (smoothDbarComponentL2 F hF hFc j)

theorem sum_smoothDbarComponent_modeParseval {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℂ) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) :
    ∑ j : Fin n, ∑' d,
        ‖gaussianHermiteMode hn d (smoothDbarComponentL2 F hF hFc j)‖ ^ 2 =
      ∑ j : Fin n, ‖smoothDbarComponentL2 F hF hFc j‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro j _
  exact smoothDbarComponent_modeParseval hn F hF hFc j

theorem dbarComponent_mul_conj {n : ℕ} {F H : Configuration n → ℂ}
    (hF : Differentiable ℝ F) (hH : Differentiable ℝ H)
    (j : Fin n) (z : Configuration n) :
    dbarComponent (fun w ↦ F w * conj (H w)) j z =
      dbarComponent F j z * conj (H z) +
        F z * dbarComponent (fun w ↦ conj (H w)) j z := by
  apply dbarComponent_mul hF
    (Complex.differentiable_conj.comp hH)

/-- The Hilbert-basis coefficient of a finite Hermite synthesis is its
algebraic coefficient. -/
theorem gaussianHermiteCoefficient_finiteHermiteCombination
    (n : ℕ) (hn : 0 < n) (c : HermiteMultiIndex n →₀ ℂ)
    (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (finiteHermiteCombination n hn c) pq = c pq := by
  rw [gaussianHermiteCoefficient_eq_inner]
  classical
  have h := inner_finiteHermiteCombination n hn (Finsupp.single pq 1) c
  have hsingle : finiteHermiteCombination n hn (Finsupp.single pq 1) =
      multivariateNormalizedL2 n hn pq.1 pq.2 := by
    simp [finiteHermiteCombination, multivariateNormalizedL2,
      ComplexHermite.hermiteL2Family]
  rw [hsingle] at h
  simpa using h

/-- The Gaussian `L²` vector represented by the `j`th `dbar` derivative of a
finite Hermite synthesis. -/
def finiteDbarComponentL2 (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  finiteHermiteCombination n hn (loweredCoefficients n c j)

theorem finiteDbarComponentL2_coeFn (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    finiteDbarComponentL2 n hn c j =ᵐ[complexGaussianMeasure n]
      dbarComponent (finiteHermiteFunction n hn c) j := by
  filter_upwards [finiteHermiteCombination_coeFn n hn
    (loweredCoefficients n c j)] with z hz
  unfold finiteDbarComponentL2
  rw [hz, ← dbarComponent_finiteHermiteFunction n hn c j z]

/-- Exact lowering/adjoint coefficient identity on the finite Hermite core. -/
theorem gaussianHermiteCoefficient_finiteDbarComponentL2
    (n : ℕ) (hn : 0 < n) (c : HermiteMultiIndex n →₀ ℂ)
    (j : Fin n) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (finiteDbarComponentL2 n hn c j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        c (raiseHermiteIndex j pq) := by
  rw [finiteDbarComponentL2,
    gaussianHermiteCoefficient_finiteHermiteCombination]
  let r := raiseHermiteIndex j pq
  have hrpos : 0 < r.2 j := by simp [r, raiseHermiteIndex, raiseAt]
  have hlower : lowerHermiteIndex j r = pq := by
    unfold r raiseHermiteIndex lowerHermiteIndex raiseAt lowerAt
    apply Prod.ext
    · rfl
    · funext k
      by_cases hkj : k = j
      · subst k
        simp
      · simp [Function.update_of_ne hkj]
  have h := loweredCoefficients_apply_lowerHermiteIndex n c j r hrpos
  rw [hlower] at h
  rw [h]
  congr 2
  simp [r, raiseHermiteIndex, raiseAt]

end

end GinibrePoincare
