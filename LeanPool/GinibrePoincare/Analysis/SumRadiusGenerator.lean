/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/SumRadiusGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.SumRadiusCoordinates

/-!
# Sum radius generator

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `complexGinibrePregenerator_sumRadiusPolynomial`.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The concrete generator restricted to polynomials in `S`, `conj S`, `R`. -/
def sumRadiusOperator (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ :=
  4 * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 Q) +
  4 * MvPolynomial.X 2 * MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 Q) +
  4 * (MvPolynomial.C (recenteredGammaShape n : ℂ) - MvPolynomial.X 2) * MvPolynomial.pderiv 2 Q -
  2 * MvPolynomial.X 0 * MvPolynomial.pderiv 0 Q -
  2 * MvPolynomial.X 1 * MvPolynomial.pderiv 1 Q

private theorem polynomial_laplacian (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ) (z : Configuration n) :
    (∑ j : Fin n, (complexSecondDirectionalDerivative (sumRadiusPolynomial n Q)
        (realCoordinateDirection j) z +
      complexSecondDirectionalDerivative (sumRadiusPolynomial n Q) (imaginaryCoordinateDirection j)
          z)) =
    4 * (n : ℂ) * sumRadiusPolynomial n (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 Q)) z +
    4 * (n : ℂ) * complexRadius n z * sumRadiusPolynomial n (MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 2 Q)) z +
    4 * (n : ℂ) * ((n : ℂ)-1) * sumRadiusPolynomial n (MvPolynomial.pderiv 2 Q) z := by
  let A (i : Fin 3) := sumRadiusPolynomial n (MvPolynomial.pderiv i Q) z
  let B (i j : Fin 3) := sumRadiusPolynomial n (MvPolynomial.pderiv j (MvPolynomial.pderiv i Q)) z
  have hsecond (v : Configuration n) :
      complexSecondDirectionalDerivative (sumRadiusPolynomial n Q) v z =
        ∑ i : Fin 3, ((∑ j : Fin 3, B i j * fderiv ℝ (sumRadiusCoordinate n j) z v) *
          fderiv ℝ (sumRadiusCoordinate n i) z v +
          A i * complexSecondDirectionalDerivative (sumRadiusCoordinate n i) v z) :=
    second_fderiv_observablePolynomial (sumRadiusCoordinate n) (differentiable_sumRadiusCoordinate
        n) v
      (fun i => differentiable_sumRadiusCoordinate_direction n i v) Q z
  have hb : B 1 0 = B 0 1 := by
    simp only [B, polynomial_pderiv_commute Q 1 0]
  have hpair (j : Fin n) :
      complexSecondDirectionalDerivative (sumRadiusPolynomial n Q) (realCoordinateDirection j) z +
      complexSecondDirectionalDerivative (sumRadiusPolynomial n Q) (imaginaryCoordinateDirection j)
          z =
        4 * B 0 1 +
        (B 0 2 + B 2 0) * (fderiv ℝ (complexRadius n) z (realCoordinateDirection j) +
          Complex.I * fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j)) +
        (B 1 2 + B 2 1) * (fderiv ℝ (complexRadius n) z (realCoordinateDirection j) -
          Complex.I * fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j)) +
        B 2 2 * ((fderiv ℝ (complexRadius n) z (realCoordinateDirection j))^2 +
          (fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j))^2) +
        4 * ((n : ℂ)-1) * A 2 := by
    have hr := hsecond (realCoordinateDirection j)
    have hi := hsecond (imaginaryCoordinateDirection j)
    rw [hr, hi]
    simp only [Fin.sum_univ_three, second_sumRadiusCoordinate_zero, second_sumRadiusCoordinate_one,
      second_sumRadiusCoordinate_two, complexRadius_realDirection, complexRadius_imaginaryDirection,
      fderiv_sumRadiusCoordinate_zero, fderiv_sumRadiusCoordinate_one,
          fderiv_sumRadiusCoordinate_two]
    simp only [realCoordinateDirection, imaginaryCoordinateDirection,
        coordinateSum_coordinateDirection,
      map_one, Complex.conj_I, mul_zero, mul_one, add_zero, hb]
    ring_nf
    simp [Complex.I_sq]; ring
  simp_rw [hpair]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ]
  change _ = 4 * (n : ℂ) * B 0 1 + 4 * (n : ℂ) * complexRadius n z * B 2 2 +
    4 * (n : ℂ) * ((n : ℂ)-1) * A 2
  have hm := radius_gradient_mixed_sum n z
  have hc := radius_gradient_conj_mixed_sum n z
  have hq := radius_gradient_square_sum n z
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hm hc hq
  linear_combination (B 0 2 + B 2 0) * hm + (B 1 2 + B 2 1) * hc + B 2 2 * hq

private theorem polynomial_confinement (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ) (z : Configuration n) :
    (∑ j : Fin n, fderiv ℝ (sumRadiusPolynomial n Q) z (coordinateDirection j (z j))) =
      sumRadiusPolynomial n (MvPolynomial.pderiv 0 Q) z * coordinateSum z +
      sumRadiusPolynomial n (MvPolynomial.pderiv 1 Q) z * conj (coordinateSum z) +
      2 * sumRadiusPolynomial n (MvPolynomial.pderiv 2 Q) z * complexRadius n z := by
  simp only [fderiv_sumRadiusPolynomial, coordinateSum_coordinateDirection,
    Finset.sum_add_distrib, ← Finset.mul_sum, complexRadius_confinement]
  rw [← map_sum]
  unfold coordinateSum
  ring

private theorem polynomial_coulomb (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ)
    (z : Configuration n) (hz : CollisionFree z) :
    (∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
      fderiv ℝ (sumRadiusPolynomial n Q) z (coulombPairDirection j k z)) =
        2 * (n : ℂ) * (vandermondeDegree n : ℂ) * sumRadiusPolynomial n (MvPolynomial.pderiv 2 Q) z
            := by
  have he (j : Fin n) (k : Fin n) (hk : k ∈ Finset.Ioi j) :
      fderiv ℝ (sumRadiusPolynomial n Q) z (coulombPairDirection j k z) =
        2 * (n : ℂ) * sumRadiusPolynomial n (MvPolynomial.pderiv 2 Q) z := by
    rw [fderiv_sumRadiusPolynomial, coordinateSum_coulombPairDirection,
      complexRadius_coulomb n z hz j k (Finset.mem_Ioi.mp hk)]
    simp
    ring
  have hh : (∑ j : Fin n, (Finset.Ioi j).card : ℕ) = vandermondeDegree n :=
    (vandermondeDegree_eq_sum_Ioi_card n).symm
  simp_rw [Finset.sum_congr rfl (fun k hk => he _ k hk), Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hh]
  ring

/-- Exact concrete generator action on every polynomial in the sum and radius coordinates. -/
theorem complexGinibrePregenerator_sumRadiusPolynomial (n : ℕ) (hn : 2 ≤ n)
    (Q : MvPolynomial (Fin 3) ℂ) (z : Configuration n) (hz : CollisionFree z) :
    complexGinibrePregenerator n (sumRadiusPolynomial n Q) z =
      sumRadiusPolynomial n (sumRadiusOperator n Q) z := by
  rw [complexGinibrePregenerator_eq_direct n _ (differentiable_sumRadiusPolynomial n Q)
    (differentiable_sumRadiusPolynomial_direction n Q)]
  unfold directComplexGinibrePregenerator
  rw [polynomial_laplacian, polynomial_confinement, polynomial_coulomb n Q z hz]
  simp only [sumRadiusPolynomial, observablePolynomial, sumRadiusOperator,
    map_add, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_ofNat,
    (show sumRadiusCoordinate n 0 = coordinateSum by rfl),
    (show sumRadiusCoordinate n 1 = (fun w => conj (coordinateSum w)) by rfl),
    (show sumRadiusCoordinate n 2 = complexRadius n by rfl)]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hshape : (recenteredGammaShape n : ℂ) = (vandermondeDegree n : ℂ) + (n : ℂ) - 1 := by
    unfold recenteredGammaShape
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  rw [hshape]
  push_cast
  field_simp
  ring

end
end GinibrePoincare
