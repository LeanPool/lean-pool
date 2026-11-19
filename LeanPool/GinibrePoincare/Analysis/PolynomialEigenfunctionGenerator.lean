/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialEigenfunctionGenerator.lean.
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
public import LeanPool.GinibrePoincare.Analysis.HermiteLaguerreOperator
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2Inverse

/-! # Concrete generator equations for the full Hermite–Laguerre family

All indices are arbitrary. The pointwise identities use the actual Ginibre
pregenerator, on collision-free configurations, at the default speed `α_n=n`
and at an explicitly rescaled speed `α`. These identities do not assert
membership in a closed generator domain.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Formal polynomial evaluation agrees with the concrete family definition. -/
theorem sumRadiusPolynomial_hermiteLaguerrePolynomial (n a b m : ℕ) (z : Configuration n) :
    sumRadiusPolynomial n (hermiteLaguerrePolynomial n a b m) z =
      polynomialEigenfunction n ⟨a, b, m⟩ z := by
  let v : Fin 3 → ℂ := fun i => sumRadiusCoordinate n i z
  have hv : v ∘ Fin.castSucc = ![SObservable z, conj (SObservable z)] := by
    funext i; fin_cases i <;> rfl
  have hH : MvPolynomial.eval v
      (hermitePolynomialLift (ComplexHermite.normalized 1 (by decide) a b)) =
      ComplexHermite.normalizedEval 1 (by decide) a b (SObservable z) := by
    simp only [hermitePolynomialLift, MvPolynomial.eval_rename, hv, ComplexHermite.normalizedEval]
  have hL : MvPolynomial.eval v (radialPolynomialLift (Laguerre.polynomial (recenteredGammaShape n)
      m)) =
      Complex.ofReal ((Laguerre.polynomial (recenteredGammaShape n) m).eval (RPoly z)) := by
    change (MvPolynomial.eval₂Hom (RingHom.id ℂ) v) _ = _
    unfold radialPolynomialLift
    rw [Polynomial.hom_eval₂]
    have hc : (MvPolynomial.eval₂Hom (RingHom.id ℂ) v).comp
        (MvPolynomial.C.comp Complex.ofRealHom) = Complex.ofRealHom := by
      ext x; simp
    rw [hc]
    simpa [v, sumRadiusCoordinate, complexRadius, RPoly] using
      (Polynomial.eval₂_hom (p := Laguerre.polynomial (recenteredGammaShape n) m)
        Complex.ofRealHom (RPoly z))
  change MvPolynomial.eval v (_ * _) = _
  rw [map_mul, hH, hL]
  rfl

/-- Full concrete generator equation at the project speed `α_n=n`. -/
theorem polynomialEigenfunction_generator (n : ℕ) (hn : 2 ≤ n)
    (ped : PolynomialEigenfunctionData n) (z : Configuration n) (hz : CollisionFree z) :
    complexGinibrePregenerator n (polynomialEigenfunction n ped) z =
      -(eigenvalue n ped.a ped.b ped.m : ℂ) * polynomialEigenfunction n ped z := by
  have heq : polynomialEigenfunction n ped =
      sumRadiusPolynomial n (hermiteLaguerrePolynomial n ped.a ped.b ped.m) := by
    funext w
    simpa using (sumRadiusPolynomial_hermiteLaguerrePolynomial n ped.a ped.b ped.m w).symm
  rw [heq, complexGinibrePregenerator_sumRadiusPolynomial n hn _ z hz,
    sumRadiusOperator_hermiteLaguerrePolynomial n ped.a ped.b ped.m hn]
  simp only [sumRadiusPolynomial, observablePolynomial, map_mul, map_neg, MvPolynomial.eval_C]
  congr 1
  simp [eigenvalue]

/-- The paper's sign convention `-A_n P = λ P`, for all indices. -/
theorem polynomialEigenfunction_eigenvalue_equation (n : ℕ) (hn : 2 ≤ n)
    (a b m : ℕ) (z : Configuration n) (hz : CollisionFree z) :
    -complexGinibrePregenerator n (polynomialEigenfunction n ⟨a, b, m⟩) z =
      (2 * ((a : ℝ) + b + 2 * m) : ℂ) * polynomialEigenfunction n ⟨a, b, m⟩ z := by
  rw [polynomialEigenfunction_generator n hn _ z hz]
  simp [eigenvalue]

/-- The full eigenvalue equation also holds almost everywhere for the actual Ginibre measure. -/
theorem polynomialEigenfunction_eigenvalue_equation_ae (n : ℕ) (hn : 2 ≤ n)
    (a b m : ℕ) :
    ∀ᵐ z ∂ginibreMeasure n,
      -complexGinibrePregenerator n (polynomialEigenfunction n ⟨a, b, m⟩) z =
        (2 * ((a : ℝ) + b + 2 * m) : ℂ) * polynomialEigenfunction n ⟨a, b, m⟩ z := by
  have hcoll : ginibreMeasure n (collisionSet n) = 0 :=
    (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n)
      (complexGaussianMeasure_collisionSet n)
  have hout : ∀ᵐ z ∂ginibreMeasure n, z ∉ collisionSet n := by
    rw [MeasureTheory.ae_iff]
    rw [show {z : Configuration n | ¬ z ∉ collisionSet n} = collisionSet n by
      ext z; simp]
    exact hcoll
  filter_upwards [hout] with z hz
  exact polynomialEigenfunction_eigenvalue_equation n hn a b m z
    ((collisionFree_iff_not_mem_collisionSet z).mpr hz)

/-- The concrete complex generator rescaled to paper speed `α`. -/
def complexGinibrePregeneratorAtSpeed (n : ℕ) (α : ℝ) (f : Configuration n → ℂ)
    (z : Configuration n) : ℂ :=
  ((α / (n : ℝ) : ℝ) : ℂ) * complexGinibrePregenerator n f z

/-- General paper-speed eigenvalue `2(α/n)(a+b+2m)`. -/
theorem polynomialEigenfunction_eigenvalue_equation_atSpeed (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (a b m : ℕ) (z : Configuration n) (hz : CollisionFree z) :
    -complexGinibrePregeneratorAtSpeed n α (polynomialEigenfunction n ⟨a, b, m⟩) z =
      (eigenvalueAtSpeed n α a b m : ℂ) * polynomialEigenfunction n ⟨a, b, m⟩ z := by
  unfold complexGinibrePregeneratorAtSpeed
  rw [polynomialEigenfunction_generator n hn _ z hz]
  simp only [eigenvalueAtSpeed, eigenvalue]
  push_cast
  ring

end
end GinibrePoincare
