/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Determinant/Filtration.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Kernel
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Basis
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The finite determinant filtration of polynomial multiplication

The first leg is kept fixed throughout. The second and third legs use the
explicit quotient/kernel vectors of `DeterminantKernel`. The coefficient
identity `adaptedTensor_reconstruct` verifies the actual multiplication on
every basis input; it does not assume a simultaneous triangularization.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation Polynomial

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

/-- Indices for the quotient and kernel parts of a determinant filtration. -/
abbrev Index (e : ℕ) := Sum (Fin (e + 2)) (Fin e)

variable (K) in
/-- The ordered quotient/kernel vectors in the actual polynomial pair space. -/
def vector (e : ℕ) : Index e → DeterminantKernel.FormPair K :=
  Sum.elim (DeterminantKernel.quotientVector e) (DeterminantKernel.kernelVector e)

variable (K) in
/-- All multiplication coefficients in the explicit adapted bases.
Here `a=d+1`, `b=e+1`, and no first-leg change of coordinates occurs. -/
def adaptedTensor (d e : ℕ) : Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inl j, .inr k =>
      if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

variable (K) in
/-- The associated graded tensor, whose two branches still share the first leg. -/
def gradedTensor (d e : ℕ) : Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | _, .inl _, .inr _ => 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

private theorem sum_coordinate {n r : ℕ} (hr : r < n)
    (v : Fin n → DeterminantKernel.FormPair K) :
    (∑ k : Fin n, (if r = k.val then (1 : K) else 0) • v k) = v ⟨r, hr⟩ := by
  have h (k : Fin n) : r = k.val ↔ k = ⟨r, hr⟩ := by
    constructor
    · intro hk
      apply Fin.ext
      exact hk.symm
    · intro hk
      exact congrArg Fin.val hk.symm
  simp_rw [h]
  simp

/-- Exact coordinate reconstruction of every first-leg slice, in common bases. -/
theorem adaptedTensor_reconstruct (d e : ℕ) (i : Fin (d + 1)) (j : Index e) :
    (∑ k : Index (d + e), adaptedTensor K d e i j k • vector K (d + e) k) =
      DeterminantKernel.multiply (X ^ i.val) (vector K e j) := by
  have hi : i.val ≤ d := by omega
  rcases j with j | j
  · by_cases hj : j.val ≤ e
    · have hn : j.val ≠ e + 1 := by omega
      simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
        Sum.elim_inr, hn, false_and, ↓reduceIte, zero_smul, Finset.sum_const_zero,
        add_zero]
      rw [sum_coordinate (by omega)]
      exact (DeterminantKernel.multiply_quotientVector_ordinary d e i.val j.val hi hj).symm
    · have hj' : j.val = e + 1 := by omega
      have hjfin : j = ⟨e + 1, by omega⟩ := Fin.ext hj'
      rw [hjfin]
      by_cases hi' : i.val < d
      · simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
          Sum.elim_inr, hi', true_and]
        rw [sum_coordinate (by omega), sum_coordinate (by omega)]
        have h := DeterminantKernel.multiply_quotientVector_top_cross
          (R := K) d e i.val hi'
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
      · have hi'' : i.val = d := by omega
        simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
          Sum.elim_inr, hi', and_false, false_and, ↓reduceIte, zero_smul,
          Finset.sum_const_zero, add_zero]
        rw [sum_coordinate (by omega)]
        have h := DeterminantKernel.multiply_quotientVector_top_last (R := K) d e
        simpa only [hi'', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
  · simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
      Sum.elim_inr, zero_smul, Finset.sum_const_zero, zero_add]
    rw [sum_coordinate (by omega)]
    exact (DeterminantKernel.multiply_kernelVector d e i.val j.val hi j.isLt).symm

/-- The reconstruction uniquely determines every tensor coefficient. -/
theorem adaptedTensor_unique (d e : ℕ)
    (T : Tensor K (Fin (d + 1)) (Index e) (Index (d + e)))
    (hT : ∀ i j, (∑ k, T i j k • vector K (d + e) k) =
      DeterminantKernel.multiply (X ^ i.val) (vector K e j)) :
    T = adaptedTensor K d e := by
  funext i j k
  have h := (DeterminantKernel.adaptedVectors_linearIndependent (R := K) (d + e))
  have hs : ∑ z, (T i j z - adaptedTensor K d e i j z) • vector K (d + e) z = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hT, adaptedTensor_reconstruct, sub_self]
  exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp h) _ hs k)

/-- The quotient branch is exactly `C(a,b+1)`. -/
theorem gradedTensor_quotient (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 2)) (k : Fin (d + e + 2)) :
    gradedTensor K d e i (.inl j) (.inl k) =
      convolution K (d + 1) (e + 2) i j (Fin.cast (by omega) k) := by
  simp only [gradedTensor, convolution, Fin.val_cast]

/-- The kernel branch is exactly `C(a,b-1)`. -/
theorem gradedTensor_kernel (d e : ℕ) (i : Fin (d + 1))
    (j : Fin e) (k : Fin (d + e)) :
    gradedTensor K d e i (.inr j) (.inr k) =
      convolution K (d + 1) e i j (Fin.cast (by omega) k) := by
  simp only [gradedTensor, convolution, Fin.val_cast]

@[simp] theorem adaptedTensor_kernel_to_quotient (d e : ℕ)
    (i : Fin (d + 1)) (j : Fin e) (k : Fin (d + e + 2)) :
    adaptedTensor K d e i (.inr j) (.inl k) = 0 := rfl

variable (K) in
/-- Polynomial diagonal maps; scaling the quotient input by `X` clears
the negative input-kernel weight without changing the leading tensor. -/
def inputScale (e : ℕ) : Index e → K[X]
  | .inl _ => X
  | .inr _ => 1

variable (K) in
/-- Scale quotient coordinates by one and kernel coordinates by the polynomial variable. -/
def outputScale (e : ℕ) : Index e → K[X]
  | .inl _ => 1
  | .inr _ => X

/-- The diagonal coordinate map with prescribed polynomial scaling factors. -/
def diagonalMap {I : Type*} [DecidableEq I] (s : I → K[X]) : I → I → K[X] :=
  fun i j => if i = j then s i else 0

private theorem restrict_diagonal {I J Q : Type*}
    [Fintype I] [Fintype J] [Fintype Q]
    [DecidableEq I] [DecidableEq J] [DecidableEq Q]
    (a : I → K[X]) (b : J → K[X]) (c : Q → K[X])
    (T : Tensor K[X] I J Q) (i : I) (j : J) (k : Q) :
    Tensor.restrict (diagonalMap a) (diagonalMap b) (diagonalMap c) T i j k =
      a i * b j * c k * T i j k := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

variable (K) in
/-- A checked polynomial degeneration to the two matched convolution branches. -/
def degeneration (d e : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (adaptedTensor K d e)
      (gradedTensor K d e) 1 0 1 1 where
  leftMap := diagonalMap (fun _ => 1)
  middleMap := diagonalMap (inputScale K e)
  rightMap := diagonalMap (outputScale K (d + e))
  left_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs <;> simp
  middle_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs
    · cases i <;> simp [inputScale]
    · simp
  right_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs
    · cases i <;> simp [outputScale]
    · simp
  vanishes := by
    intro i j k n hn
    have hn' : n = 0 := by omega
    rw [restrict_diagonal]
    rcases j with j | j <;> rcases k with k | k
    all_goals simp only [inputScale, outputScale, adaptedTensor, one_mul]
    all_goals (try split_ifs) <;> simp [hn', ← pow_two]
  leading := by
    intro i j k
    rw [restrict_diagonal]
    rcases j with j | j <;> rcases k with k | k
    all_goals simp only [inputScale, outputScale, adaptedTensor, gradedTensor, one_mul]
    all_goals (try split_ifs) <;> simp [← pow_two]

/-! The actual coordinate change from the original two-copy convolution. -/

/-- Indices for the two original monomial bases before the filtration change of basis. -/
abbrev OriginalIndex (e : ℕ) := Sum (Fin (e + 1)) (Fin (e + 1))

variable (K) in
/-- The original monomial bases in the `s` and `w` components. -/
def originalBasis (e : ℕ) :
    Module.Basis (OriginalIndex e) K (DeterminantBasis.BoundedPair K e) :=
  (Polynomial.degreeLT.basis K (e + 1)).prod (Polynomial.degreeLT.basis K (e + 1))

theorem degree_shift_lt (d e : ℕ) (i : Fin (d + 1))
    (p : Polynomial.degreeLT K (e + 1)) :
    ((X : K[X]) ^ i.val * (p : K[X])).degree < (d + e + 1 : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · have hp := Polynomial.mem_degreeLT.mp p.2
    rw [Polynomial.degree_lt_iff_coeff_zero] at hp
    exact hp (n - i.val) (by have hi := i.isLt; omega)
  · rfl

variable (K) in
/-- Multiplication by a fixed first-input monomial between the bounded spaces. -/
def boundedShift (d e : ℕ) (i : Fin (d + 1)) :
    Polynomial.degreeLT K (e + 1) →ₗ[K] Polynomial.degreeLT K (d + e + 1) where
  toFun p := ⟨X ^ i.val * (p : K[X]), Polynomial.mem_degreeLT.mpr (degree_shift_lt d e i p)⟩
  map_add' p q := by apply Subtype.ext; simp [mul_add]
  map_smul' c p := by apply Subtype.ext; simp [Polynomial.smul_eq_C_mul]; ring

variable (K) in
/-- The same first monomial multiplies both components. -/
def boundedMultiply (d e : ℕ) (i : Fin (d + 1)) :
    DeterminantBasis.BoundedPair K e →ₗ[K] DeterminantBasis.BoundedPair K (d + e) :=
  (boundedShift K d e i).prodMap (boundedShift K d e i)

@[simp] theorem forget_boundedMultiply (d e : ℕ) (i : Fin (d + 1))
    (p : DeterminantBasis.BoundedPair K e) :
    DeterminantBasis.forget (d + e) (boundedMultiply K d e i p) =
      DeterminantKernel.multiply (X ^ i.val) (DeterminantBasis.forget e p) := rfl

variable (K) in
/-- Polynomial multiplication in its original monomial coordinates. -/
def sourceTensor (d e : ℕ) :
    Tensor K (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e)) :=
  fun i j k => (originalBasis K (d + e)).repr
    (boundedMultiply K d e i (originalBasis K e j)) k

@[simp] theorem sourceTensor_inl_inl (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor K d e i (.inl j) (.inl k) =
      convolution K (d + 1) (e + 1) i j (Fin.cast (by omega) k) := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift,
    ← pow_add, convolution, eq_comm]

@[simp] theorem sourceTensor_inr_inr (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor K d e i (.inr j) (.inr k) =
      convolution K (d + 1) (e + 1) i j (Fin.cast (by omega) k) := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift,
    ← pow_add, convolution, eq_comm]

@[simp] theorem sourceTensor_inl_inr (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor K d e i (.inl j) (.inr k) = 0 := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift]

@[simp] theorem sourceTensor_inr_inl (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor K d e i (.inr j) (.inl k) = 0 := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift]

/-- Record the polynomial coordinate and the choice of `s` or `w` separately. -/
def originalCoordinate (e : ℕ) : OriginalIndex e → Fin (e + 1) × Bool
  | .inl j => (j, false)
  | .inr j => (j, true)

/-- The source is exactly polynomial convolution tensored with a two-coordinate
dot product whose singleton is on the unchanged first leg. -/
theorem sourceTensor_product (d e : ℕ) :
    sourceTensor K d e =
      Tensor.pullback (fun i : Fin (d + 1) => (i, ())) (originalCoordinate e)
        (fun k => (Fin.cast (by omega) (originalCoordinate (d + e) k).1,
          (originalCoordinate (d + e) k).2))
        (Tensor.product (convolution K (d + 1) (e + 1))
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))) := by
  funext i j k
  rcases j with j | j <;> rcases k with k | k <;>
    simp [Tensor.pullback, Tensor.product, Tensor.cyclic, Tensor.dotPairing,
      originalCoordinate]

variable (K) in
/-- The input matrix has adapted vectors as columns in the original basis. -/
def inputChange (e : ℕ) (j : Index e) (old : OriginalIndex e) : K :=
  (originalBasis K e).repr (DeterminantBasis.basis K e j) old

variable (K) in
/-- The output-dual matrix uses the inverse basis change, as required for tensors. -/
def outputDualChange (e : ℕ) (k : Index e) (old : OriginalIndex e) : K :=
  (DeterminantBasis.basis K e).repr (originalBasis K e old) k

variable (K) in
/-- The first input is unchanged, including throughout the basis change. -/
def fixedFirst (d : ℕ) (i j : Fin (d + 1)) : K := if i = j then 1 else 0

private theorem restrict_fixedFirst (d e : ℕ)
    (B : Index e → OriginalIndex e → K)
    (C : Index (d + e) → OriginalIndex (d + e) → K)
    (T : Tensor K (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e)))
    (i : Fin (d + 1)) (j : Index e) (k : Index (d + e)) :
    Tensor.restrict (fixedFirst K d) B C T i j k =
      ∑ y, ∑ z, B j y * C k z * T i y z := by
  simp [Tensor.restrict, fixedFirst, ite_mul]

theorem boundedMultiply_adapted_coordinates (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    (DeterminantBasis.basis K (d + e)).repr
      (boundedMultiply K d e i (DeterminantBasis.basis K e j)) k =
      adaptedTensor K d e i j k := by
  have h := adaptedTensor_unique d e
    (fun i j k => (DeterminantBasis.basis K (d + e)).repr
      (boundedMultiply K d e i (DeterminantBasis.basis K e j)) k) ?_
  · exact congrFun (congrFun (congrFun h i) j) k
  · intro i j
    have hsum := congrArg (DeterminantBasis.forget (R := K) (d + e))
      ((DeterminantBasis.basis K (d + e)).sum_repr
        (boundedMultiply K d e i (DeterminantBasis.basis K e j)))
    simpa only [map_sum, map_smul, DeterminantBasis.forget_basis,
      forget_boundedMultiply, vector] using hsum

/-- A concrete restriction, with the identity first map, changes the original
two-copy convolution into the simultaneously triangular coefficient tensor. -/
theorem sourceTensor_coordinate_change (d e : ℕ) :
    Tensor.restrict (fixedFirst K d) (inputChange K e) (outputDualChange K (d + e))
      (sourceTensor K d e) = adaptedTensor K d e := by
  funext i j k
  rw [restrict_fixedFirst]
  simp only [inputChange, outputDualChange, sourceTensor]
  calc
    (∑ y, ∑ z,
        (originalBasis K e).repr (DeterminantBasis.basis K e j) y *
          (DeterminantBasis.basis K (d + e)).repr (originalBasis K (d + e) z) k *
          (originalBasis K (d + e)).repr (boundedMultiply K d e i (originalBasis K e y)) z) =
        ∑ y, (originalBasis K e).repr (DeterminantBasis.basis K e j) y *
          (DeterminantBasis.basis K (d + e)).repr
            (boundedMultiply K d e i (originalBasis K e y)) k := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      exact (DeterminantBasis.basis K (d + e)).sum_repr_mul_repr
        (originalBasis K (d + e)) _ k
    _ = (DeterminantBasis.basis K (d + e)).repr
          (boundedMultiply K d e i (DeterminantBasis.basis K e j)) k := by
      have hsum := congrArg (fun p => (DeterminantBasis.basis K (d + e)).repr
          (boundedMultiply K d e i p) k)
        ((originalBasis K e).sum_repr (DeterminantBasis.basis K e j))
      simpa only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
        smul_eq_mul] using hsum
    _ = adaptedTensor K d e i j k := boundedMultiply_adapted_coordinates d e i j k

end MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

end

end MatrixMultiplicationAllFields
