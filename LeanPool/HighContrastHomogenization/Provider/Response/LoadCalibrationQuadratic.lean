/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationSchur
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers

/-!
# High-contrast homogenization: Provider.Response.LoadCalibrationQuadratic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quadratic forms in Schur coordinates

The load displays of the response-load calibration are quadratic forms of
the terminal block at the two signed profile vectors, so they need the Schur
factorization read on vectors rather than on matrices.  This file supplies that
reading, once:

    (X, Y) ⬝ schurBlock s s_* k (X, Y) = ⟨sX, X⟩ + ⟨s_*⁻¹(Y - kX), Y - kX⟩,

together with the elementary facts the recentering step uses: the shear acts on
a doubled vector by `G_c (X, Y) = (X, cX + Y)`, a skew matrix annihilates its
own quadratic form, and `⟨m^{-1/2}e, m^{1/2}e⟩ = ⟨e, e⟩`.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Doubled vectors -/

/-- The quadratic form of a diagonal doubled block. -/
theorem quadratic_fromBlocks_diag (A C : Mat d) (X Y : Vec d) :
    Sum.elim X Y ⬝ᵥ (Matrix.fromBlocks A 0 0 C : FullBlockMat d) *ᵥ Sum.elim X Y =
      X ⬝ᵥ A *ᵥ X + Y ⬝ᵥ C *ᵥ Y := by
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- The shear acts on a doubled vector by `G_c (X, Y) = (X, cX + Y)`. -/
theorem fullBlockShear_mulVec (c : Mat d) (X Y : Vec d) :
    fullBlockShear c *ᵥ Sum.elim X Y = Sum.elim X (c *ᵥ X + Y) := by
  rw [fullBlockShear, Matrix.fromBlocks_mulVec]
  simp

/-- **The quadratic form of the Schur factorization.** -/
theorem quadratic_schurBlock (s sStar k : Mat d) (X Y : Vec d) :
    Sum.elim X Y ⬝ᵥ schurBlock s sStar k *ᵥ Sum.elim X Y =
      X ⬝ᵥ s *ᵥ X + (Y - k *ᵥ X) ⬝ᵥ sStar⁻¹ *ᵥ (Y - k *ᵥ X) := by
  have hv : (-k) *ᵥ X + Y = Y - k *ᵥ X := by
    rw [Matrix.neg_mulVec]
    abel
  rw [schurBlock, Initialization.quad_conj, fullBlockShear_mulVec, hv, quadratic_fromBlocks_diag]

/-! ## Pairings -/

/-- The pairing of two matrix images, moved onto one side. -/
theorem dotProduct_mulVec_pair (A B : Mat d) (x y : Vec d) :
    (A *ᵥ x) ⬝ᵥ (B *ᵥ y) = x ⬝ᵥ (Aᵀ * B) *ᵥ y := by
  conv_rhs =>
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **A skew matrix annihilates its own quadratic form.** -/
theorem dotProduct_mulVec_of_skew {W : Mat d} (hW : Wᴴ = -W) (x : Vec d) :
    x ⬝ᵥ W *ᵥ x = 0 := by
  have hT : Wᵀ = -W := by rw [← conjTranspose_eq_transpose', hW]
  have h : x ⬝ᵥ W *ᵥ x = (Wᵀ *ᵥ x) ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [hT, Matrix.neg_mulVec, neg_dotProduct] at h
  have hc : (W *ᵥ x) ⬝ᵥ x = x ⬝ᵥ W *ᵥ x := dotProduct_comm _ _
  rw [hc] at h
  linarith only [h]

/-- **Polarization**: the two cross terms cancel. -/
theorem polarization {n : Type*} [Fintype n] (T : Matrix n n ℝ)
    (u v : n → ℝ) :
    (u + v) ⬝ᵥ T *ᵥ (u + v) + (u - v) ⬝ᵥ T *ᵥ (u - v) =
      2 * (u ⬝ᵥ T *ᵥ u) + 2 * (v ⬝ᵥ T *ᵥ v) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  ring

/-- **The load pairing is the Euclidean pairing**:
`⟨m^{-1/2}e, m^{1/2}e⟩ = ⟨e, e⟩`. -/
theorem dotProduct_load_pair {m : Mat d} (hm : m.PosDef) (e : Vec d) :
    (matSqrt m⁻¹ *ᵥ e) ⬝ᵥ (matSqrt m *ᵥ e) = e ⬝ᵥ e := by
  have hsymm : (matSqrt m⁻¹)ᵀ = matSqrt m⁻¹ := by
    rw [← conjTranspose_eq_transpose', conjTranspose_matSqrt hm.inv.posSemidef]
  rw [dotProduct_mulVec_pair, hsymm, matSqrt_inv_mul_matSqrt hm, Matrix.one_mulVec]

end

end Response
end HighContrast
end HCPolySupport
