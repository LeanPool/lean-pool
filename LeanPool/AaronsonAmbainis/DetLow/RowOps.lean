/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.DetLow.Basic

/-!
# DetLow: `(1 - s_j^2)^(e_j)` divides the determinant of the agreement matrix

This is Lemma 3.5 of the paper.
Row operations: with `P[x,y] = 1` if `x j = true` and `y = x^j` (and `0` otherwise),
`(1 + s_j P) (1 - s_j P) = 1` and `(1 - s_j P) M = D N`, where `D` is diagonal with entry
`1 - s_j^2` at the rows `x ∈ Up g j` and `1` elsewhere. (In the proof of the paper the matrices
`P`, `D`, `N` are called `E`, `Λ`, `M~`.)
-/

@[expose] public section

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Splitting off the `j`-th factor of `agMon`. -/
theorem agMon_eq_mul_erase (x z : Cube ι) (j : ι) :
    agMon x z = (if x j = z j then X j else 1) *
      ∏ i ∈ univ.erase j, (if x i = z i then (X i : MvPolynomial ι ℤ) else 1) := by
  unfold agMon
  exact (Finset.mul_prod_erase univ _ (mem_univ j)).symm

theorem prod_erase_flipSet (x z : Cube ι) (j : ι) :
    ∏ i ∈ univ.erase j, (if flipSet x {j} i = z i then (X i : MvPolynomial ι ℤ) else 1)
      = ∏ i ∈ univ.erase j, (if x i = z i then (X i : MvPolynomial ι ℤ) else 1) := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [flipSet_singleton_of_ne x (Finset.ne_of_mem_erase hi)]

/-- If `x` and `z` agree at `j` then `M[x,z] = s_j * M[x^j,z]`. -/
theorem agMon_of_eq (x z : Cube ι) (j : ι) (h : x j = z j) :
    agMon x z = X j * agMon (flipSet x {j}) z := by
  have hne : ¬ (flipSet x {j} j = z j) := by
    rw [flipSet_singleton_self, ← h]
    cases x j <;> simp
  rw [agMon_eq_mul_erase x z j, agMon_eq_mul_erase (flipSet x {j}) z j, prod_erase_flipSet,
    ite_eq_left h, ite_eq_right hne, one_mul]

/-- If `x` and `z` disagree at `j` then `M[x^j,z] = s_j * M[x,z]`. -/
theorem agMon_of_ne (x z : Cube ι) (j : ι) (h : x j ≠ z j) :
    agMon (flipSet x {j}) z = X j * agMon x z := by
  have heq : flipSet x {j} j = z j := by
    rw [flipSet_singleton_self]
    revert h
    cases x j <;> cases z j <;> simp
  rw [agMon_eq_mul_erase x z j, agMon_eq_mul_erase (flipSet x {j}) z j, prod_erase_flipSet,
    ite_eq_right h, ite_eq_left heq, one_mul]

/-- `P[x,y] = 1` if `x j = true` and `y = x^j`, and `0` otherwise. -/
noncomputable def pairMat (g : Cube ι → Bool) (j : ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x y => if x.1 j = true ∧ y.1 = flipSet x.1 {j} then 1 else 0

/-- `N[x,z] = 0` if `x ∈ Up g j` and `z j = x j`, and `M[x,z]` otherwise. -/
noncomputable def redMat (g : Cube ι → Bool) (j : ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => if x ∈ Up g j ∧ z.1 j = x.1 j then 0 else agMon x.1 z.1

/-- The diagonal of `D`: `1 - s_j^2` on `Up g j`, `1` elsewhere. -/
noncomputable def diagVec (g : Cube ι → Bool) (j : ι) : Ones g → MvPolynomial ι ℤ :=
  fun x => if x ∈ Up g j then 1 - X j ^ 2 else 1

theorem pairMat_apply (g : Cube ι → Bool) (j : ι) (x y : Ones g) :
    pairMat g j x y = if x.1 j = true ∧ y.1 = flipSet x.1 {j} then 1 else 0 := rfl

omit [DecidableEq ι] in
theorem agMatrix_apply (g : Cube ι → Bool) (x z : Ones g) :
    agMatrix g x z = agMon x.1 z.1 := rfl

theorem pairMat_mul_pairMat (g : Cube ι → Bool) (j : ι) : pairMat g j * pairMat g j = 0 := by
  apply Matrix.ext
  intro x z
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro y _
  rw [pairMat_apply, pairMat_apply]
  by_cases h : x.1 j = true ∧ y.1 = flipSet x.1 {j}
  · have hy : ¬ (y.1 j = true ∧ z.1 = flipSet y.1 {j}) := by
      rintro ⟨hy1, -⟩
      have hf : y.1 j = false := by
        rw [h.2, flipSet_singleton_self, h.1]
        rfl
      rw [hf] at hy1
      exact Bool.false_ne_true hy1
    rw [ite_eq_right hy, mul_zero]
  · rw [ite_eq_right h, zero_mul]

theorem pairMat_mul_agMatrix (g : Cube ι → Bool) (j : ι) (x z : Ones g) :
    (pairMat g j * agMatrix g) x z =
      if x ∈ Up g j then agMon (flipSet x.1 {j}) z.1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hx : x ∈ Up g j
  · rw [ite_eq_left hx]
    have hx' := mem_Up.mp hx
    rw [Finset.sum_eq_single (⟨flipSet x.1 {j}, hx'.2⟩ : Ones g)]
    · rw [pairMat_apply, agMatrix_apply, ite_eq_left ⟨hx'.1, rfl⟩, one_mul]
    · intro y _ hy
      rw [pairMat_apply, ite_eq_right, zero_mul]
      rintro ⟨-, h2⟩
      exact hy (Subtype.ext h2)
    · intro h
      exact absurd (mem_univ _) h
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro y _
    rw [pairMat_apply, ite_eq_right, zero_mul]
    rintro ⟨h1, h2⟩
    apply hx
    rw [mem_Up]
    refine ⟨h1, ?_⟩
    rw [← h2]
    exact y.2

theorem unipotent_mul (g : Cube ι → Bool) (j : ι) :
    (1 + (X j : MvPolynomial ι ℤ) • pairMat g j) * (1 - (X j : MvPolynomial ι ℤ) • pairMat g j)
      = 1 := by
  have h : ((X j : MvPolynomial ι ℤ) • pairMat g j) * ((X j : MvPolynomial ι ℤ) • pairMat g j)
      = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, pairMat_mul_pairMat, smul_zero, smul_zero]
  rw [mul_sub, mul_one, add_mul, one_mul, h, add_zero, add_sub_cancel_right]

theorem rowop_eq (g : Cube ι → Bool) (j : ι) :
    (1 - (X j : MvPolynomial ι ℤ) • pairMat g j) * agMatrix g
      = Matrix.diagonal (diagVec g j) * redMat g j := by
  apply Matrix.ext
  intro x z
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    pairMat_mul_agMatrix, Matrix.diagonal_mul, smul_eq_mul, agMatrix_apply]
  simp only [diagVec, redMat]
  by_cases hx : x ∈ Up g j
  · by_cases hz : z.1 j = x.1 j
    · rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left ⟨hx, hz⟩, mul_zero,
        agMon_of_eq x.1 z.1 j hz.symm,
        sub_self]
    · rw [ite_eq_left hx, ite_eq_left hx, ite_eq_right (fun h => hz h.2),
        agMon_of_ne x.1 z.1 j (fun h => hz h.symm)]
      ring
  · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right (fun h => hx h.1), mul_zero, sub_zero,
      one_mul]

theorem prod_diagVec (g : Cube ι → Bool) (j : ι) :
    ∏ x, diagVec g j x = (1 - X j ^ 2) ^ (Up g j).card := by
  unfold diagVec
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- Lemma 3.5 of the paper: `det M = (1 - s_j^2)^(e_j) * R` for some polynomial `R`. -/
theorem det_factor (g : Cube ι → Bool) (j : ι) :
    ∃ R : MvPolynomial ι ℤ, (agMatrix g).det = (1 - X j ^ 2) ^ (Up g j).card * R := by
  refine ⟨(1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det * (redMat g j).det, ?_⟩
  have h1 := congrArg Matrix.det (unipotent_mul g j)
  have h2 := congrArg Matrix.det (rowop_eq g j)
  rw [Matrix.det_mul, Matrix.det_one] at h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_diagVec] at h2
  calc (agMatrix g).det
      = (1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det *
          ((1 - (X j : MvPolynomial ι ℤ) • pairMat g j).det * (agMatrix g).det) := by
        rw [← mul_assoc, h1, one_mul]
    _ = (1 - X j ^ 2) ^ (Up g j).card *
          ((1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det * (redMat g j).det) := by
        rw [h2]
        ring

end DetLow
end AaronsonAmbainis
