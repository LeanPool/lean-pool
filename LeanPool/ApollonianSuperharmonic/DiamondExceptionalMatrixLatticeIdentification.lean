/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondExceptionalLattice
public import LeanPool.ApollonianSuperharmonic.DiamondPeakMatrix
public import LeanPool.ApollonianSuperharmonic.IntegralityLattice
public meta import Lean.Meta.Tactic.NormCast
public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Data.EReal.Inv

-- [TABLET NODE: DiamondExceptionalMatrixLatticeIdentification]

/-!
# DiamondExceptionalMatrixLatticeIdentification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondExceptionalMatrixLatticeIdentification (K : DiamondParameter)
    (C : BandCircle) (hC : C.1.1 = (DiamondRecursiveQuadruple K) 0) :
    CircleMatrix C = DiamondPeakMatrix K ∧
      IntegralityLattice C = DiamondExceptionalLattice K := by
-- BODY
  have hk : (0 : ℝ) < K.1 := by exact_mod_cast K.2
  have hmatrix :
      CircleMatrix C =
        let c : ℝ := C.1.1.1
        let x : ℝ := C.1.1.2.re
        let y : ℝ := C.1.1.2.im
        (2 * c)⁻¹ • ![![1 + x, y], ![y, 1 - x]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CircleMatrix, BandCircleEuclideanData]
    all_goals field_simp
  have matrixIdentity : CircleMatrix C = DiamondPeakMatrix K := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hmatrix, DiamondPeakMatrix, hC, DiamondRecursiveQuadruple]
      <;> field_simp; ring
  constructor
  · exact matrixIdentity
  · ext u
    constructor
    · intro hu
      change ∀ i : Fin 2, ∃ n : ℤ,
        Matrix.mulVec (CircleMatrix C)
          ![((u.re : ℤ) : ℝ), ((u.im : ℤ) : ℝ)] i = (n : ℝ) at hu
      rw [matrixIdentity] at hu
      have first := hu 0
      have second := hu 1
      simp only [Matrix.mulVec, DiamondPeakMatrix, Nat.succ_eq_add_one, Nat.reduceAdd,
          one_div, Matrix.smul_cons, smul_eq_mul, mul_one, Matrix.smul_empty, Fin.isValue,
          Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Int.reduceNeg,
          GaussianInt.intCast_re, GaussianInt.intCast_im, Matrix.dotProduct_cons,
          Matrix.head_cons, Matrix.tail_cons, Matrix.dotProduct_of_isEmpty, add_zero,
          Matrix.cons_val_one] at first second
      rcases first with ⟨n, first⟩
      rcases second with ⟨m, second⟩
      field_simp at first second
      rw [← GaussianInt.intCast_re u, ← GaussianInt.intCast_im u] at first second
      change (K.1 : ℝ) * (u.re : ℝ) + (K.1 + 1) * (u.im : ℝ) =
          2 * (K.1 + 1) * n at first
      change (K.1 : ℝ) * (u.re : ℝ) + (u.im : ℝ) * (1 - K.1) =
          2 * K.1 * m at second
      have firstZ : (K.1 : ℤ) * u.re + (K.1 + 1) * u.im =
          2 * (K.1 + 1) * n := by exact_mod_cast first
      have secondZ : (K.1 : ℤ) * u.re + u.im * (1 - K.1) =
          2 * K.1 * m := by exact_mod_cast second
      have copNat : (K.val + 1).Coprime K.val := by
        simp []
      have cop : IsCoprime (K.1 + 1 : ℤ) K.1 :=
        Nat.Coprime.isCoprime copNat
      have productDiv : (K.1 + 1 : ℤ) ∣ (K.1 : ℤ) * u.re := by
        refine ⟨2 * n - u.im, ?_⟩
        linarith [firstZ]
      have aDiv : (K.1 + 1 : ℤ) ∣ u.re :=
        cop.dvd_of_dvd_mul_left productDiv
      obtain ⟨q, hq⟩ := aDiv
      have bDiv : (K.1 : ℤ) ∣ u.im := by
        refine ⟨2 * m - u.re + u.im, ?_⟩
        linarith [secondZ]
      obtain ⟨t, ht⟩ := bDiv
      have firstReduced : (K.1 : ℤ) * (q + t) = 2 * n := by
        apply (mul_left_cancel₀ (show (K.1 + 1 : ℤ) ≠ 0 by omega))
        rw [hq, ht] at firstZ
        linarith [firstZ]
      have secondReduced : (K.1 + 1 : ℤ) * q + (1 - K.1) * t = 2 * m := by
        have hkz : (K.1 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt K.2)
        apply (mul_left_cancel₀ hkz)
        rw [hq, ht] at secondZ
        linarith [secondZ]
      have parity : q + t = 2 * (m - n + K.1 * t) := by
        linarith [firstReduced, secondReduced]
      have huform : u = q • (⟨(K.1 + 1 : ℤ), K.1⟩ : GaussianInt) +
          (q - m + n - K.1 * t) • (⟨0, -(2 * K.1 : ℤ)⟩ : GaussianInt) := by
        apply Zsqrtd.ext
        · simp [hq]; ring
        · simp [ht]
          nlinarith [parity]
      rw [huform]
      apply (DiamondExceptionalLattice K).add_mem
      · exact (DiamondExceptionalLattice K).zsmul_mem
          (AddSubgroup.mem_closure_of_mem (by right; rfl)) q
      · exact (DiamondExceptionalLattice K).zsmul_mem
          (AddSubgroup.mem_closure_of_mem (by left; rfl)) (q - m + n - K.1 * t)
    · intro hu
      change u ∈ AddSubgroup.closure
        {v | v = (⟨0, -(2 * K.1 : Int)⟩ : GaussianInt) ∨
          v = (⟨(K.1 + 1 : Int), (K.1 : Int)⟩ : GaussianInt)} at hu
      induction hu using AddSubgroup.closure_induction with
      | mem v hv =>
          change ∀ i : Fin 2, ∃ n : ℤ,
            Matrix.mulVec (CircleMatrix C)
              ![((v.re : ℤ) : ℝ), ((v.im : ℤ) : ℝ)] i = (n : ℝ)
          rcases hv with rfl | rfl
          · intro i
            fin_cases i
            · refine ⟨-(K.1 : ℤ), ?_⟩
              rw [matrixIdentity]
              simp [DiamondPeakMatrix, Matrix.mulVec]
            · refine ⟨(K.1 : ℤ) - 1, ?_⟩
              rw [matrixIdentity]
              simp [DiamondPeakMatrix, Matrix.mulVec]
              field_simp
              ring
          · intro i
            fin_cases i
            · refine ⟨(K.1 : ℤ), ?_⟩
              rw [matrixIdentity]
              simp [DiamondPeakMatrix, Matrix.mulVec]
              field_simp
              ring
            · refine ⟨1, ?_⟩
              rw [matrixIdentity]
              simp [DiamondPeakMatrix, Matrix.mulVec]
              field_simp
              ring
      | zero =>
          exact (IntegralityLattice C).zero_mem
      | add x y hx hy ihx ihy =>
          exact (IntegralityLattice C).add_mem ihx ihy
      | neg x hx ih =>
          exact (IntegralityLattice C).neg_mem ih

end ApollonianSuperharmonic

end
