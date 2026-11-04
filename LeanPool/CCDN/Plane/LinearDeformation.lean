/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! Constant and first coefficients of a plane equation under a linear
one-parameter displacement of one coordinate. These are algebraic coefficient
identities, valid for arbitrary commutative target algebras. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma polynomial_plane_coeff_one_chain {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (ψ : MvPolynomial (Fin 2) K →ₐ[K] Polynomial A)
    (f : MvPolynomial (Fin 2) K) :
    (ψ f).coeff 1 = (ψ (pderiv 0 f)).coeff 0 * (ψ (X 0)).coeff 1 +
      (ψ (pderiv 1 f)).coeff 0 * (ψ (X 1)).coeff 1 := by
  have hC (c : K) : ψ (C c) = Polynomial.C (algebraMap K A c) := ψ.commutes c
  induction f using MvPolynomial.induction_on with
  | C c => simp [hC]
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg]; ring
  | mul_X f k hf =>
    fin_cases k <;>
      simp [map_mul, Derivation.leibniz, smul_eq_mul, Polynomial.mul_coeff_zero,
        Polynomial.mul_coeff_one, hf] <;> ring

/-- Vary one plane coordinate by t*w in an arbitrary target algebra. -/
def planeLinearDeformation {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a : Fin 2 → A) (k : Fin 2) (w : A) :
    MvPolynomial (Fin 2) K →ₐ[K] Polynomial A :=
  aeval (fun j => Polynomial.C (a j) + if j = k then Polynomial.X * Polynomial.C w else 0)

/-- The constant coefficient of the linear deformation of `f` at `a` is the value `f(a)`. -/
lemma planeLinearDeformation_coeff_zero {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (a : Fin 2 → A) (k : Fin 2) (w : A)
    (f : MvPolynomial (Fin 2) K) :
    (planeLinearDeformation a k w f).coeff 0 = aeval a f := by
  have hC (c : K) : planeLinearDeformation a k w (C c) =
      Polynomial.C (algebraMap K A c) := (planeLinearDeformation a k w).commutes c
  have hX (j : Fin 2) : (planeLinearDeformation (K := K) a k w (X j)).coeff 0 = a j := by
    fin_cases j <;> fin_cases k <;> simp [planeLinearDeformation]
  induction f using MvPolynomial.induction_on with
  | C c => simp only [hC, Polynomial.coeff_C_zero, aeval_C]
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg]
  | mul_X f j hf => simp only [map_mul, Polynomial.mul_coeff_zero, hf, hX, aeval_X]

/-- The linear coefficient of the deformation of `f` at `a` along coordinate `k` with speed `w` is
`(∂f/∂x_k)(a) * w`. -/
lemma planeLinearDeformation_coeff_one {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (a : Fin 2 → A) (k : Fin 2) (w : A)
    (f : MvPolynomial (Fin 2) K) :
    (planeLinearDeformation a k w f).coeff 1 = aeval a (pderiv k f) * w := by
  rw [polynomial_plane_coeff_one_chain, planeLinearDeformation_coeff_zero,
    planeLinearDeformation_coeff_zero]
  fin_cases k <;> simp [planeLinearDeformation, Polynomial.mul_coeff_one]

end
end CCDN
