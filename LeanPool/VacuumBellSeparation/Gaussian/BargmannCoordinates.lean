/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.TypeStar

/-!
# Bargmann quadrature coordinates

The explicit complex coordinate transformation at the start of Appendix A of
the manuscript. The two
copies of the index type label first the `q` and then the `p` coordinates.

This module proves the matrix identities for `D_B` and the real-vector identity
`D_B (conj z, z) = sqrt 2 (Re z, Im z)`.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exchange matrix `S_B = [0,I; I,0]`. -/
def bargmannSwap : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 1 1 0

/-- The unscaled Bargmann coordinate matrix `[I,I; iI,-iI]`. -/
def unscaledBargmannD : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 1 1 (Complex.I • 1) ((-Complex.I) • 1)

/-- The Appendix A coordinate transformation
`D_B = (1 / sqrt 2) [I,I; iI,-iI]`. -/
noncomputable def bargmannD : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • unscaledBargmannD

/-- The bilinear Gram matrix of the unscaled transformation. -/
theorem unscaledBargmannD_transpose_mul :
    (unscaledBargmannD (n := n))ᵀ * unscaledBargmannD =
      (2 : ℂ) • bargmannSwap := by
  simp only [unscaledBargmannD, bargmannSwap, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_smul, transpose_one, transpose_smul,
    Matrix.mul_smul, smul_smul, mul_one]
  congr 1 <;> simp [two_smul ℂ]

/-- The Hermitian Gram matrix of the unscaled transformation. -/
theorem unscaledBargmannD_conjTranspose_mul :
    (unscaledBargmannD (n := n))ᴴ * unscaledBargmannD = (2 : ℂ) • 1 := by
  rw [unscaledBargmannD, fromBlocks_conjTranspose, fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [conjTranspose_smul, smul_smul, two_smul ℂ]

private theorem bargmann_scale_sq :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2 = 1 := by
  have hs : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Complex.ofReal_inv]
  rw [← mul_inv, ← pow_two, hs]
  norm_num

/-- The identity `D_Bᵀ D_B = S_B` used to derive the Bargmann kernel from
the coherent-state diagonal. The transpose here is deliberately bilinear,
not conjugate-transpose. -/
theorem bargmannD_transpose_mul :
    (bargmannD (n := n))ᵀ * bargmannD = bargmannSwap := by
  rw [bargmannD, transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    unscaledBargmannD_transpose_mul, smul_smul, smul_smul,
    bargmann_scale_sq, one_smul]

/-- The coordinate transformation is unitary. -/
theorem bargmannD_conjTranspose_mul :
    (bargmannD (n := n))ᴴ * bargmannD = 1 := by
  rw [bargmannD, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    unscaledBargmannD_conjTranspose_mul]
  have hs : star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) :=
    RCLike.conj_ofReal _
  simp only [hs, smul_smul, ← mul_assoc,
    bargmann_scale_sq, one_smul]

/-- A conjugate pair of complex coordinates `(conj z, z)`. -/
def conjugatePair (z : n → ℂ) : n ⊕ n → ℂ :=
  Sum.elim (fun j => star (z j)) z

/-- The real phase-space coordinate vector `sqrt 2 (Re z, Im z)`, included
in complex coordinate space. -/
noncomputable def coherentQuadratures (z : n → ℂ) : n ⊕ n → ℂ :=
  Sum.elim (fun j => ((Real.sqrt 2 * (z j).re : ℝ) : ℂ))
    (fun j => ((Real.sqrt 2 * (z j).im : ℝ) : ℂ))

/-- The manuscript's exact real-coordinate identity
`D_B (conj z, z) = sqrt 2 (Re z, Im z)`. -/
theorem bargmannD_mulVec_conjugatePair (z : n → ℂ) :
    bargmannD *ᵥ conjugatePair z = coherentQuadratures z := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hscale : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
    calc
      _ = (Real.sqrt 2)⁻¹ * (Real.sqrt 2 * Real.sqrt 2) := by rw [hs]
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  ext j
  rcases j with j | j
  · simp only [bargmannD, unscaledBargmannD, smul_mulVec, fromBlocks_mulVec,
      one_mulVec, conjugatePair, coherentQuadratures, Pi.smul_apply, Pi.add_apply,
      Function.comp_apply, Sum.elim_inl, Sum.elim_inr, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im];
      nlinarith [hscale]
  · simp only [bargmannD, unscaledBargmannD, smul_mulVec, fromBlocks_mulVec,
      one_mulVec, conjugatePair, coherentQuadratures, Pi.smul_apply, Pi.add_apply,
      Function.comp_apply, Sum.elim_inl, Sum.elim_inr, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im];
      nlinarith [hscale]

end VacuumBellSeparation.Gaussian
