/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ForMathlib.IntegerPolynomialL1
public import LeanPool.CCDN.Noether.AmbientNoetherForms
import LeanPool.CCDN.Noether.UniversalPlaneL1

/-!
The printed coefficient-sum bound for the ambient Noether forms.
Coefficient extraction from plane parameters costs no additional factor.

The sharp printed coefficient-sum bound for the plane Noether minors:
each entry has l1 norm at most d, hence the order d²−1 determinant has
l1 norm at most d^(3d²−3).
-/

@[expose] public section
namespace CCDN
noncomputable section

private lemma factorial_mul_degree_pow_le (d r : ℕ) (hr : r ≤ d ^ 2) :
    r.factorial * d ^ r ≤ d ^ (3 * r) := by
  calc
    r.factorial * d ^ r ≤ r ^ r * d ^ r :=
      Nat.mul_le_mul_right _ (Nat.factorial_le_pow r)
    _ ≤ (d ^ 2) ^ r * d ^ r :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hr r)
    _ = d ^ (3 * r) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma ambientEulerEntry_flatten_l1_le (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℕ) (row : ℕ × ℕ) (col : EulerColumns k) :
    l1Norm ((sumAlgEquiv ℤ (PlaneParameters σ) (Sym σ (k + 2))).symm
      (ambientEulerEntryLinear _ σ k row col (universalHomogeneousForm σ (k + 2)))) ≤
      Fintype.card (Sym σ (k + 2)) * ((k + 2) * 3 ^ (k + 2)) := by
  classical
  rw [universalHomogeneousForm_linear_expansion, map_sum, map_sum]
  apply (l1Norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Sym σ (k + 2), (k + 2) * 3 ^ (k + 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, ambientEulerEntryLinear_map, smul_eq_C_mul]
      exact (l1Norm_sumAlgEquiv_symm_C_X_mul_map_C_le _ i).trans
        (ambientEulerEntry_monomial_l1_le k _ (homogeneousCoefficientExponent_degree _ _ _) row col)
    _ = _ := by simp

private theorem ambientNoetherParameterMinor_flatten_l1_le
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℕ) (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    l1Norm ((sumAlgEquiv ℤ (PlaneParameters σ) (Sym σ (k + 2))).symm
      (ambientNoetherParameterMinor σ k rows cols)) ≤
      (k + 2) ^ (3 * (k + 2) ^ 2 - 3) *
        (Fintype.card (Sym σ (k + 2)) * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1) := by
  classical
  let r := (k + 2) ^ 2 - 1
  let N := Fintype.card (Sym σ (k + 2))
  let φ := (sumAlgEquiv ℤ (PlaneParameters σ) (Sym σ (k + 2))).symm.toRingHom
  change l1Norm (φ
    (((eulerClosedFormCoefficientMatrix k
      (universalPlanePolynomial (universalHomogeneousForm σ (k + 2))))).submatrix
        rows cols).det) ≤ _
  rw [RingHom.map_det]
  have hdet := l1Norm_det_le _ (N * ((k + 2) * 3 ^ (k + 2)))
    (fun i j => ambientEulerEntry_flatten_l1_le σ k (rows i) (cols j))
  rw [Fintype.card_fin] at hdet
  apply hdet.trans
  have he : 3 * r = 3 * (k + 2) ^ 2 - 3 := by dsimp [r]; omega
  calc
    r.factorial * (N * ((k + 2) * 3 ^ (k + 2))) ^ r =
        (r.factorial * (k + 2) ^ r) * (N * 3 ^ (k + 2)) ^ r := by
      rw [show N * ((k + 2) * 3 ^ (k + 2)) = (k + 2) * (N * 3 ^ (k + 2)) by ring,
        mul_pow]
      ring
    _ ≤ (k + 2) ^ (3 * r) * (N * 3 ^ (k + 2)) ^ r :=
      Nat.mul_le_mul_right _ (factorial_mul_degree_pow_le (k + 2) r (by dsimp [r]; omega))
    _ = _ := by rw [he]

/-- The exact coefficient-sum bound, in terms of the number of original
degree-d homogeneous monomials. -/
theorem ambientNoetherForm_coefficientL1_le
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℕ) (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k)
    (m : PlaneParameters σ →₀ ℕ) :
    l1Norm (ambientNoetherForm σ k rows cols m) ≤
      (k + 2) ^ (3 * (k + 2) ^ 2 - 3) *
        (Fintype.card (Sym σ (k + 2)) * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1) :=
  (l1Norm_coeff_le_l1Norm_sumAlgEquiv_symm _ _).trans
    (ambientNoetherParameterMinor_flatten_l1_le σ k rows cols)

end
end CCDN
