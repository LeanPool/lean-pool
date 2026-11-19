/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteLaguerreOperator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.SumRadiusGenerator
public import LeanPool.GinibrePoincare.Analysis.HermiteOrnsteinUhlenbeck
public import LeanPool.GinibrePoincare.Analysis.GeneralizedLaguerre

/-!
# Hermite Laguerre operator

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `sumRadiusOperator_hermiteLaguerrePolynomial`.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Embed the Hermite variables as the first two of the three joint coordinates. -/
def hermitePolynomialLift (P : ComplexHermite.Poly) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.rename Fin.castSucc P

/-- Embed a real polynomial in the third, radius coordinate. -/
def radialPolynomialLift (P : Polynomial ℝ) : MvPolynomial (Fin 3) ℂ :=
  P.eval₂ (MvPolynomial.C.comp Complex.ofRealHom) (MvPolynomial.X 2)

@[simp] theorem pderiv_zero_hermitePolynomialLift (P : ComplexHermite.Poly) :
    MvPolynomial.pderiv 0 (hermitePolynomialLift P) =
      hermitePolynomialLift (MvPolynomial.pderiv 0 P) :=
  MvPolynomial.pderiv_rename (Fin.castSucc_injective 2) (0 : Fin 2) P

@[simp] theorem pderiv_one_hermitePolynomialLift (P : ComplexHermite.Poly) :
    MvPolynomial.pderiv 1 (hermitePolynomialLift P) =
      hermitePolynomialLift (MvPolynomial.pderiv 1 P) :=
  MvPolynomial.pderiv_rename (Fin.castSucc_injective 2) (1 : Fin 2) P

@[simp] theorem pderiv_two_hermitePolynomialLift (P : ComplexHermite.Poly) :
    MvPolynomial.pderiv 2 (hermitePolynomialLift P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [hermitePolynomialLift]
  | add P Q hP hQ =>
    rw [hermitePolynomialLift, map_add, map_add]
    rw [hermitePolynomialLift] at hP hQ
    rw [hP, hQ, add_zero]
  | mul_X P i hP =>
    simp only [hermitePolynomialLift, map_mul, MvPolynomial.rename_X, MvPolynomial.pderiv_mul]
    fin_cases i <;> simp_all [hermitePolynomialLift, MvPolynomial.pderiv_X]

/-- The radius embedding intertwines formal derivatives. -/
theorem pderiv_radialPolynomialLift (P : Polynomial ℝ) (i : Fin 3) :
    MvPolynomial.pderiv i (radialPolynomialLift P) =
      if i = 2 then radialPolynomialLift P.derivative else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [radialPolynomialLift, Polynomial.eval₂_add, map_add] at hP hQ ⊢
      rw [hP, hQ]
      split_ifs <;> simp
  | monomial m a =>
      simp only [radialPolynomialLift, Polynomial.eval₂_monomial, RingHom.comp_apply,
        Complex.ofRealHom, Polynomial.derivative_monomial, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_C, zero_mul, zero_add, MvPolynomial.pderiv_pow,
        MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> simp_all [map_mul, map_natCast]; ring

@[simp] theorem pderiv_zero_radialPolynomialLift (P : Polynomial ℝ) :
    MvPolynomial.pderiv 0 (radialPolynomialLift P) = 0 := by
  simp [pderiv_radialPolynomialLift]

@[simp] theorem pderiv_one_radialPolynomialLift (P : Polynomial ℝ) :
    MvPolynomial.pderiv 1 (radialPolynomialLift P) = 0 := by
  simp [pderiv_radialPolynomialLift]

@[simp] theorem pderiv_two_radialPolynomialLift (P : Polynomial ℝ) :
    MvPolynomial.pderiv 2 (radialPolynomialLift P) = radialPolynomialLift P.derivative := by
  simp [pderiv_radialPolynomialLift]

/-- The actual formal Hermite–Laguerre polynomial in the three joint coordinates. -/
def hermiteLaguerrePolynomial (n a b m : ℕ) : MvPolynomial (Fin 3) ℂ :=
  hermitePolynomialLift (ComplexHermite.normalized 1 (by decide) a b) *
    radialPolynomialLift (Laguerre.polynomial (recenteredGammaShape n) m)

private theorem sumRadiusOperator_tensor (n a b m : ℕ) (H : ComplexHermite.Poly) (L : Polynomial ℝ)
    (hHermite : 4 * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 H) -
      2 * (ComplexHermite.Z * MvPolynomial.pderiv 0 H + ComplexHermite.W * MvPolynomial.pderiv 1 H)
          =
        -2 * ((a + b : ℕ) : ComplexHermite.Poly) * H)
    (hLaguerre : Laguerre.operator (recenteredGammaShape n) L = -Polynomial.C (m : ℝ) * L) :
    sumRadiusOperator n (hermitePolynomialLift H * radialPolynomialLift L) =
      -MvPolynomial.C (2 * ((a : ℂ) + b + 2 * m)) * (hermitePolynomialLift H * radialPolynomialLift
          L) := by
  have hH := congrArg (fun P : ComplexHermite.Poly => hermitePolynomialLift P)
    hHermite
  simp only [hermitePolynomialLift, map_sub, map_mul, map_add, map_neg, map_ofNat, map_natCast,
      MvPolynomial.rename_X,
    ComplexHermite.Z, ComplexHermite.W] at hH
  change 4 * hermitePolynomialLift (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 H)) -
    2 * (MvPolynomial.X 0 * hermitePolynomialLift (MvPolynomial.pderiv 0 H) +
      MvPolynomial.X 1 * hermitePolynomialLift (MvPolynomial.pderiv 1 H)) =
        -2 * ((a+b : ℕ) : MvPolynomial (Fin 3) ℂ) * hermitePolynomialLift H at hH
  have hL := congrArg radialPolynomialLift
    hLaguerre
  simp only [radialPolynomialLift, Laguerre.operator, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_neg,
    RingHom.comp_apply, Complex.ofRealHom] at hL
  change MvPolynomial.X 2 * radialPolynomialLift L.derivative.derivative +
    (MvPolynomial.C (recenteredGammaShape n : ℂ) - MvPolynomial.X 2) * radialPolynomialLift
        L.derivative =
      -(MvPolynomial.C (m : ℂ)) * radialPolynomialLift L at hL
  change sumRadiusOperator n (hermitePolynomialLift H * radialPolynomialLift L) =
    -MvPolynomial.C (2 * ((a : ℂ) + b + 2 * m)) * (hermitePolynomialLift H * radialPolynomialLift L)
  simp only [sumRadiusOperator, MvPolynomial.pderiv_mul, 
    pderiv_zero_hermitePolynomialLift, pderiv_one_hermitePolynomialLift,
    pderiv_two_hermitePolynomialLift, pderiv_zero_radialPolynomialLift,
    pderiv_one_radialPolynomialLift, pderiv_two_radialPolynomialLift,
    zero_mul, mul_zero, add_zero, zero_add]
  simp only [map_mul, map_add, map_natCast, map_ofNat, Nat.cast_add] at hH hL ⊢
  linear_combination radialPolynomialLift L * hH + 4 * hermitePolynomialLift H * hL

/-- Algebraic eigenvalue equation for the operator obtained from the concrete generator. -/
theorem sumRadiusOperator_hermiteLaguerrePolynomial (n a b m : ℕ) (hn : 2 ≤ n) :
    sumRadiusOperator n (hermiteLaguerrePolynomial n a b m) =
      -MvPolynomial.C (2 * ((a : ℂ) + b + 2 * m)) * hermiteLaguerrePolynomial n a b m :=
  sumRadiusOperator_tensor n a b m _ _ (ComplexHermite.ornsteinUhlenbeck_normalized a b)
    (Laguerre.operator_polynomial (recenteredGammaShape n) m (recenteredGammaShape_pos n hn))

end
end GinibrePoincare
