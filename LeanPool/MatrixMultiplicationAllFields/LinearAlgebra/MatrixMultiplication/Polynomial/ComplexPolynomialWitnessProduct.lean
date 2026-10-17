/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialRestriction
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation
namespace Tensor
namespace PolynomialApproximation

variable {F X Y Z U V W X' Y' Z' : Type*} [Field F]
variable {T : Tensor F X Y Z} {S : Tensor F U V W}
variable {r s d e D E : ℕ}

theorem product_polynomial_eq (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) (x : X × U) (y : Y × V) (z : Z × W) :
    Tensor.product A.polynomial B.polynomial x y z =
      Polynomial.X ^ (d + e) * Tensor.product A.normalized B.normalized x y z := by
  dsimp only [Tensor.product]
  rw [A.polynomial_eq, B.polynomial_eq, pow_add]
  ring

def product (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) :
    PolynomialApproximation (Tensor.product T S) (r * s) (d + e) (D + E) where
  polynomial := Tensor.product A.polynomial B.polynomial
  rank_bound := A.rank_bound.product B.rank_bound
  vanishes := by
    intro x y z k hk
    rw [A.product_polynomial_eq B]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false]
  leading := by
    intro x y z
    rw [A.product_polynomial_eq B]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      Tensor.product, Polynomial.mul_coeff_zero, A.normalized_constant, B.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    exact Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_le_of_degree_le (A.degree_bound x.1 y.1 z.1))
      (Polynomial.natDegree_le_of_degree_le (B.degree_bound x.2 y.2 z.2))

@[simp] theorem product_polynomial (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) :
    (A.product B).polynomial = Tensor.product A.polynomial B.polynomial := rfl

def productExact (A : PolynomialApproximation T r d D)
    (S : Tensor F U V W) (s : ℕ) (hS : RankAtMost S s) :
    PolynomialApproximation (Tensor.product T S) (r * s) d D := by
  simpa only [Nat.add_zero] using A.product (ofRankAtMost S s hS)

def pullback (A : PolynomialApproximation T r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    PolynomialApproximation (Tensor.pullback fx fy fz T) r d D where
  polynomial := Tensor.pullback fx fy fz A.polynomial
  rank_bound := A.rank_bound.pullback fx fy fz
  vanishes := fun x y z k hk => A.vanishes (fx x) (fy y) (fz z) k hk
  leading := fun x y z => A.leading (fx x) (fy y) (fz z)
  degree_bound := fun x y z => A.degree_bound (fx x) (fy y) (fz z)

@[simp] theorem pullback_polynomial (A : PolynomialApproximation T r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    (A.pullback fx fy fz).polynomial = Tensor.pullback fx fy fz A.polynomial := rfl

def cyclic (A : PolynomialApproximation T r d D) :
    PolynomialApproximation (Tensor.cyclic T) r d D where
  polynomial := Tensor.cyclic A.polynomial
  rank_bound := A.rank_bound.cyclic
  vanishes := fun y z x k hk => A.vanishes x y z k hk
  leading := fun y z x => A.leading x y z
  degree_bound := fun y z x => A.degree_bound x y z

@[simp] theorem cyclic_polynomial (A : PolynomialApproximation T r d D) :
    A.cyclic.polynomial = Tensor.cyclic A.polynomial := rfl

def directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : ι → Tensor F X Y Z} {S : κ → Tensor F U V W}
    (A : PolynomialApproximation (Tensor.directSum T) r d D)
    (B : PolynomialApproximation (Tensor.directSum S) s e E) :
    PolynomialApproximation
      (Tensor.directSum (fun i : ι × κ => Tensor.product (T i.1) (S i.2)))
      (r * s) (d + e) (D + E) := by
  have h := (A.product B).pullback (directSumProductEquiv ι κ X U)
    (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
  simpa only [Tensor.directSum_product] using h

def directSum_pullback {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor F X Y Z}
    (A : PolynomialApproximation (Tensor.directSum T) r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    PolynomialApproximation
      (Tensor.directSum (fun i => Tensor.pullback fx fy fz (T i))) r d D :=
  A.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

def directSum_cyclic {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor F X Y Z}
    (A : PolynomialApproximation (Tensor.directSum T) r d D) :
    PolynomialApproximation (Tensor.directSum (fun i => Tensor.cyclic (T i))) r d D := by
  simpa only [Tensor.cyclic_directSum] using A.cyclic

section Rectangular

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

def matrixCoefficients_symmetrized
    (P : PolynomialApproximation (matrixCoefficients (K := F) A B C) r d D) :
    PolynomialApproximation
      (matrixCoefficients (K := F) (A × B × C) (A × B × C) (A × B × C))
      (r ^ 3) (3 * d) (3 * D) := by
  have h := ((P.product P.cyclic).product P.cyclic.cyclic).pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  have hd : d + d + d = 3 * d := by ring
  have hD : D + D + D = 3 * D := by ring
  simpa only [Tensor.cyclic_matrixCoefficients, Tensor.matrixCoefficients_cyclic_product_square,
    pow_succ, pow_zero, one_mul, hd, hD] using h

def matrixCoefficients_directSum_symmetrized {ι : Type*} [DecidableEq ι]
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := F) A B C)) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : (ι × ι) × ι =>
        matrixCoefficients (K := F) (A × B × C) (A × B × C) (A × B × C)))
      (r ^ 3) (3 * d) (3 * D) := by
  have P₁ : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := F) B C A)) r d D := by
    simpa only [Tensor.cyclic_matrixCoefficients] using P.directSum_cyclic
  have P₂ : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := F) C A B)) r d D := by
    simpa only [Tensor.cyclic_matrixCoefficients] using P₁.directSum_cyclic
  have h := ((P.directSum_product P₁).directSum_product P₂).directSum_pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  have hd : d + d + d = 3 * d := by ring
  have hD : D + D + D = 3 * D := by ring
  simpa only [Tensor.matrixCoefficients_cyclic_product_square,
    pow_succ, pow_zero, one_mul, hd, hD] using h

end Rectangular

end PolynomialApproximation
end Tensor
end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
