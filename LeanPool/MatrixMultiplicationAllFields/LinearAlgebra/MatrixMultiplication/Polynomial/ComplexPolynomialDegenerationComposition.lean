/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import Mathlib.Algebra.Polynomial.Expand
public import Lean.Elab.Tactic.Omega

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section ScalarRestriction

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]
variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_scalar_mul (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (P : Tensor K X Y Z) (s : K) :
    restrict A B C (fun x y z => s * P x y z) =
      fun x' y' z' => s * restrict A B C P x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem cyclic_restrict (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (P : Tensor K X Y Z) :
    cyclic (restrict A B C P) = restrict B C A (cyclic P) := by
  funext y' z' x'
  simp only [cyclic, restrict]
  calc
    (∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * P x y z) =
        ∑ y, ∑ x, ∑ z, A x' x * B y' y * C z' z * P x y z :=
      Finset.sum_comm
    _ = ∑ y, ∑ z, ∑ x, A x' x * B y' y * C z' z * P x y z := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro x hx
      ring

end ScalarRestriction

section PolynomialCoefficients

variable {F : Type*} [Field F]

theorem coeff_mul_expand_eq_constant (M p : Polynomial F) (a : F)
    (hp : p.coeff 0 = a) (k j : ℕ) (hj : j ≤ k) :
    (M * Polynomial.expand F (k + 1) p).coeff j =
      (M * Polynomial.C a).coeff j := by
  have hdiv : Polynomial.X ∣ p - Polynomial.C a :=
    Polynomial.X_dvd_iff.mpr (by simp only [Polynomial.coeff_sub,
      Polynomial.coeff_C_zero, hp, sub_self])
  rcases hdiv with ⟨q, hq⟩
  have hpq : p = Polynomial.C a + Polynomial.X * q := by
    rw [← hq]
    ring
  have hexpand : Polynomial.expand F (k + 1) p =
      Polynomial.C a + Polynomial.X ^ (k + 1) *
        Polynomial.expand F (k + 1) q := by
    rw [hpq, map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X]
  have hmul : M * Polynomial.expand F (k + 1) p =
      M * Polynomial.C a + Polynomial.X ^ (k + 1) *
        (M * Polynomial.expand F (k + 1) q) := by
    rw [hexpand]
    ring
  rw [hmul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    ite_eq_right (by omega), add_zero]

end PolynomialCoefficients

section PolynomialLocalMaps

variable {F X Y Z X' Y' Z' : Type*} [Field F]
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Polynomial coordinate maps certifying a restriction degeneration with controlled
degrees. -/
structure PolynomialRestrictionDegeneration
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k Lx Ly Lz : ℕ) where
  /-- Polynomial coordinate map on the first tensor leg. -/
  leftMap : X' → X → Polynomial F
  /-- Polynomial coordinate map on the second tensor leg. -/
  middleMap : Y' → Y → Polynomial F
  /-- Polynomial coordinate map on the third tensor leg. -/
  rightMap : Z' → Z → Polynomial F
  left_degree : ∀ x' x, (leftMap x' x).degree ≤ Lx
  middle_degree : ∀ y' y, (middleMap y' y).degree ≤ Ly
  right_degree : ∀ z' z, (rightMap z' z).degree ≤ Lz
  vanishes : ∀ x' y' z' j, j < k →
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff j = 0
  leading : ∀ x' y' z',
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff k = U x' y' z'

namespace PolynomialRestrictionDegeneration

variable {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'}
variable {k Lx Ly Lz r d D : ℕ}

/-- Cyclically permute the legs of a certified polynomial restriction degeneration. -/
def cyclic (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    PolynomialRestrictionDegeneration (Tensor.cyclic T) (Tensor.cyclic U) k Ly Lz Lx where
  leftMap := L.middleMap
  middleMap := L.rightMap
  rightMap := L.leftMap
  left_degree := L.middle_degree
  middle_degree := L.right_degree
  right_degree := L.left_degree
  vanishes := by
    intro y' z' x' j hj
    change (restrict L.middleMap L.rightMap L.leftMap
      (Tensor.cyclic (fun x y z => Polynomial.C (T x y z))) y' z' x').coeff j = 0
    rw [← cyclic_restrict]
    exact L.vanishes x' y' z' j hj
  leading := by
    intro y' z' x'
    change (restrict L.middleMap L.rightMap L.leftMap
      (Tensor.cyclic (fun x y z => Polynomial.C (T x y z))) y' z' x').coeff k =
        Tensor.cyclic U y' z' x'
    rw [← cyclic_restrict]
    exact L.leading x' y' z'

/-- Apply the degeneration's polynomial coordinate maps to the original tensor. -/
def basePolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap (fun x y z => Polynomial.C (T x y z))

/-- Compose a restriction degeneration with an approximation after expanding its polynomial
variable. -/
def compositionPolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) : Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap
    (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z))

/-- Compose the degeneration with the normalized approximation after expanding its variable. -/
def normalizedComposition (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) : Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap
    (fun x y z => Polynomial.expand F (k + 1) (W.normalized x y z))

theorem compositionPolynomial_eq
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (x' : X') (y' : Y') (z' : Z') :
    L.compositionPolynomial W x' y' z' =
      Polynomial.X ^ (d * (k + 1)) * L.normalizedComposition W x' y' z' := by
  have hpoint : (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z)) =
      fun x y z => Polynomial.X ^ (d * (k + 1)) *
        Polynomial.expand F (k + 1) (W.normalized x y z) := by
    funext x y z
    rw [W.polynomial_eq, map_mul, map_pow, Polynomial.expand_X]
    simp only [← pow_mul, Nat.mul_comm]
  unfold compositionPolynomial normalizedComposition
  rw [hpoint, restrict_scalar_mul]

theorem normalizedComposition_coeff
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (j : ℕ) (hj : j ≤ k)
    (x' : X') (y' : Y') (z' : Z') :
    (L.normalizedComposition W x' y' z').coeff j =
      (L.basePolynomial x' y' z').coeff j := by
  simp only [normalizedComposition, basePolynomial, restrict, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  exact coeff_mul_expand_eq_constant
    (L.leftMap x' x * L.middleMap y' y * L.rightMap z' z)
    (W.normalized x y z) (T x y z) (W.normalized_constant x y z) k j hj

theorem compositionPolynomial_rank
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    RankAtMost (L.compositionPolynomial W) r :=
  (W.rank_bound.map (Polynomial.expand F (k + 1)).toRingHom).restrict
    L.leftMap L.middleMap L.rightMap

theorem compositionPolynomial_degree
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (x' : X') (y' : Y') (z' : Z') :
    (L.compositionPolynomial W x' y' z').degree ≤ D * (k + 1) + Lx + Ly + Lz := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold compositionPolynomial restrict
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y hy
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z hz
  have hA := Polynomial.natDegree_le_of_degree_le (L.left_degree x' x)
  have hB := Polynomial.natDegree_le_of_degree_le (L.middle_degree y' y)
  have hC := Polynomial.natDegree_le_of_degree_le (L.right_degree z' z)
  have hP : (Polynomial.expand F (k + 1) (W.polynomial x y z)).natDegree ≤
      D * (k + 1) := by
    rw [Polynomial.natDegree_expand]
    exact Nat.mul_le_mul_right (k + 1)
      (Polynomial.natDegree_le_of_degree_le (W.degree_bound x y z))
  have hprod := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le hA hB) hC) hP
  change (L.leftMap x' x * L.middleMap y' y * L.rightMap z' z *
    Polynomial.expand F (k + 1) (W.polynomial x y z)).natDegree ≤
      D * (k + 1) + Lx + Ly + Lz
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprod

/-- Construct the composed polynomial approximation with explicit rank and degree bounds. -/
def compose (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    PolynomialApproximation U r (d * (k + 1) + k) (D * (k + 1) + Lx + Ly + Lz) where
  polynomial := L.compositionPolynomial W
  rank_bound := L.compositionPolynomial_rank W
  vanishes := by
    intro x' y' z' j hj
    rw [L.compositionPolynomial_eq W, Polynomial.coeff_X_pow_mul']
    split_ifs with hdj
    · have hjk : j - d * (k + 1) < k := by omega
      rw [L.normalizedComposition_coeff W _ (Nat.le_of_lt hjk)]
      exact L.vanishes x' y' z' _ hjk
    · rfl
  leading := by
    intro x' y' z'
    rw [L.compositionPolynomial_eq W, Polynomial.coeff_X_pow_mul']
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
    rw [L.normalizedComposition_coeff W k le_rfl]
    exact L.leading x' y' z'
  degree_bound := L.compositionPolynomial_degree W

@[simp] theorem compose_polynomial
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    (L.compose W).polynomial = restrict L.leftMap L.middleMap L.rightMap
      (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z)) := rfl

end PolynomialRestrictionDegeneration

end PolynomialLocalMaps

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
