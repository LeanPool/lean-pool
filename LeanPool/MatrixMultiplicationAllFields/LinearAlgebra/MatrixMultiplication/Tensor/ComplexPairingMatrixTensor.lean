/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K : Type*} [CommSemiring K]

/-- Remove the singleton factor from the first leg of a dot-pairing matrix tensor. -/
def dotPairingMatrixX (U : Type*) : (Unit × U) ≃ U where
  toFun x := x.2
  invFun x := ((), x)
  left_inv := by rintro ⟨⟨⟩, x⟩; rfl
  right_inv x := rfl

/-- Remove the singleton factor from the second leg of a dot-pairing matrix tensor. -/
def dotPairingMatrixY (U : Type*) : (U × Unit) ≃ U where
  toFun y := y.1
  invFun y := (y, ())
  left_inv := by rintro ⟨y, ⟨⟩⟩; rfl
  right_inv y := rfl

/-- Identify the singleton third-leg coordinate spaces of the dot-pairing matrix tensor. -/
def dotPairingMatrixZ : (Unit × Unit) ≃ Unit where
  toFun _ := ()
  invFun _ := ((), ())
  left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
  right_inv := by rintro ⟨⟩; rfl

theorem dotPairing_matrixCoefficients (U : Type*) [DecidableEq U] :
    pullback (dotPairingMatrixX U) (dotPairingMatrixY U) dotPairingMatrixZ
      (dotPairing (K := K) U) = matrixCoefficients Unit U Unit := by
  funext x y z
  change (if x.2 = y.1 then (1 : K) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) ↔ x.2 = y.1 :=
    ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  by_cases hxy : x.2 = y.1
  · calc
      (if x.2 = y.1 then (1 : K) else 0) = 1 := ite_eq_left hxy
      _ = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) :=
        (ite_eq_left (hguard.mpr hxy)).symm
  · have hfull : ¬ (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
      fun h => hxy (hguard.mp h)
    calc
      (if x.2 = y.1 then (1 : K) else 0) = 0 := ite_eq_right hxy
      _ = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) :=
        (ite_eq_right hfull).symm

theorem matrixCoefficients_rank_of_dotPairing {U : Type*} [DecidableEq U] {r : ℕ}
    (h : RankAtMost (dotPairing (K := K) U) r) :
    RankAtMost (matrixCoefficients (K := K) Unit U Unit) r := by
  have h' := h.pullback (dotPairingMatrixX U) (dotPairingMatrixY U) dotPairingMatrixZ
  rw [dotPairing_matrixCoefficients] at h'
  exact h'

theorem matrixCoefficients_borderRank_of_dotPairing
    {U : Type*} [DecidableEq U] {r : ℕ}
    (h : BorderRankAtMost (dotPairing (K := ℂ) U) r) :
    BorderRankAtMost (matrixCoefficients (K := ℂ) Unit U Unit) r := by
  classical
  rw [← dotPairing_matrixCoefficients]
  exact h.pullback _ _ _

/-- Product of three cyclically positioned dot-pairing tensors. -/
def pairingTriple (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K ((B × A) × Unit) ((B × Unit) × C) ((Unit × A) × C) :=
  product (product (dotPairing B) (cyclic (dotPairing A)))
    (cyclic (cyclic (dotPairing C)))

/-- Reindex the first matrix-coordinate pair for the triple dot-pairing representation. -/
def pairingTripleMatrixX (A B : Type*) : (A × B) ≃ ((B × A) × Unit) where
  toFun x := ((x.2, x.1), ())
  invFun x := (x.1.2, x.1.1)
  left_inv x := rfl
  right_inv := by rintro ⟨⟨b, a⟩, ⟨⟩⟩; rfl

/-- Reindex the second matrix-coordinate pair for the triple dot-pairing representation. -/
def pairingTripleMatrixY (B C : Type*) : (B × C) ≃ ((B × Unit) × C) where
  toFun y := ((y.1, ()), y.2)
  invFun y := (y.1.1, y.2)
  left_inv y := rfl
  right_inv := by rintro ⟨⟨b, ⟨⟩⟩, c⟩; rfl

/-- Reindex the third matrix-coordinate pair for the triple dot-pairing representation. -/
def pairingTripleMatrixZ (C A : Type*) : (C × A) ≃ ((Unit × A) × C) where
  toFun z := (((), z.2), z.1)
  invFun z := (z.2, z.1.2)
  left_inv z := rfl
  right_inv := by rintro ⟨⟨⟨⟩, a⟩, c⟩; rfl

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem pairingTriple_matrixCoefficients :
    pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
      (pairingTripleMatrixZ C A) (pairingTriple (K := K) A B C) =
      matrixCoefficients A B C := by
  funext x y z
  change ((if x.2 = y.1 then (1 : K) else 0) *
    (if z.2 = x.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : ((x.2 = y.1 ∧ z.2 = x.1) ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

theorem matrixCoefficients_rank_of_pairingTriple {r : ℕ}
    (h : RankAtMost (pairingTriple (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) A B C) r := by
  have h' := h.pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
    (pairingTripleMatrixZ C A)
  rw [pairingTriple_matrixCoefficients] at h'
  exact h'

theorem matrixCoefficients_borderRank_of_pairingTriple
       {r : ℕ}
    (h : BorderRankAtMost (pairingTriple (K := ℂ) A B C) r) :
    BorderRankAtMost (matrixCoefficients (K := ℂ) A B C) r := by
  classical
  rw [← pairingTriple_matrixCoefficients]
  exact h.pullback _ _ _

theorem matrixCoefficients_directSum_rank_of_pairingTriple
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => pairingTriple (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r := by
  have h' := h.directSumPullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
    (pairingTripleMatrixZ C A)
  simpa only [pairingTriple_matrixCoefficients] using h'

theorem matrixCoefficients_directSum_borderRank_of_pairingTriple
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : BorderRankAtMost (directSum (fun _ : ι => pairingTriple (K := ℂ) A B C)) r) :
    BorderRankAtMost (directSum (fun _ : ι => matrixCoefficients (K := ℂ) A B C)) r := by
  classical
  have heq := directSumPullback (fun _ : ι => pairingTriple (K := ℂ) A B C)
    (pairingTripleMatrixX A B) (pairingTripleMatrixY B C) (pairingTripleMatrixZ C A)
  simp only [pairingTriple_matrixCoefficients] at heq
  rw [← heq]
  exact h.pullback _ _ _

end Tensor
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
