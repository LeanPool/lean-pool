/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.GeometricMeanToolkit

/-!
# High-contrast homogenization: Geometry.Sharp

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp involution and the shear

On a doubled block matrix the reference text sets `R := (0 I; I 0)`, the swap
matrix of `s.scale.selection`, and `H^♯ := R H^{-1} R`, and writes
`G_h := (I 0; h I)` for the shear.  This file fixes both on the flattened carrier
`FullBlockMat d`, where the doubled index type is a sum type and
`Matrix.fromBlocks` is available, and proves the rules for the primal-adjoint
involution together with its invariance under a constant skew shear: the sharp
map is an involution, it reverses the Loewner order, it is homogeneous of degree
minus one, and it commutes with congruence by a shear along a skew matrix.

The recentering identity rests on the two displayed identities of the reference
proof, `R G_h^{-1} = G_h^t R` and `G_h^{-t} R = R G_h`, valid exactly because `h`
is skew.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- The reflection `R = (0 I; I 0)` of `s.scale.selection`. -/
@[expose]
def fullBlockRefl (d : ℕ) : FullBlockMat d :=
  Matrix.fromBlocks 0 1 1 0

/-- The shear `G_h = (I 0; h I)`. -/
@[expose]
def fullBlockShear (h : Mat d) : FullBlockMat d :=
  Matrix.fromBlocks 1 0 h 1

/-- The primal-adjoint involution `H^♯ = R H^{-1} R`. -/
@[expose]
def fullBlockSharp (H : FullBlockMat d) : FullBlockMat d :=
  fullBlockRefl d * H⁻¹ * fullBlockRefl d

/-! ## The reflection -/

@[simp] theorem fullBlockRefl_mul_self : fullBlockRefl d * fullBlockRefl d = 1 := by
  rw [fullBlockRefl, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

@[simp] theorem conjTranspose_fullBlockRefl :
    (fullBlockRefl d)ᴴ = fullBlockRefl d := by
  rw [fullBlockRefl, Matrix.fromBlocks_conjTranspose]
  simp

theorem isUnit_fullBlockRefl : IsUnit (fullBlockRefl d) :=
  ⟨⟨fullBlockRefl d, fullBlockRefl d, fullBlockRefl_mul_self, fullBlockRefl_mul_self⟩, rfl⟩

theorem isUnit_det_fullBlockRefl : IsUnit (fullBlockRefl d).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp isUnit_fullBlockRefl

@[simp] theorem fullBlockRefl_inv : (fullBlockRefl d)⁻¹ = fullBlockRefl d :=
  Matrix.inv_eq_right_inv fullBlockRefl_mul_self

/-- Conjugation by the reflection preserves positive definiteness. -/
theorem posDef_refl_conj {H : FullBlockMat d} (hH : H.PosDef) :
    (fullBlockRefl d * H * fullBlockRefl d).PosDef := by
  have hc := hH.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (isUnit_fullBlockRefl (d := d)))
  rwa [conjTranspose_fullBlockRefl] at hc

/-- Conjugation by the reflection is monotone. -/
theorem refl_conj_le_refl_conj {H K : FullBlockMat d} (h : H ≤ K) :
    fullBlockRefl d * H * fullBlockRefl d ≤ fullBlockRefl d * K * fullBlockRefl d :=
  conj_le_conj' conjTranspose_fullBlockRefl h

/-! ## The sharp involution -/

/-- The sharp of a positive definite block is positive definite. -/
theorem posDef_fullBlockSharp {H : FullBlockMat d} (hH : H.PosDef) :
    (fullBlockSharp H).PosDef :=
  posDef_refl_conj hH.inv

/-- **The sharp map is an involution**. -/
theorem fullBlockSharp_fullBlockSharp {H : FullBlockMat d} (hH : H.PosDef) :
    fullBlockSharp (fullBlockSharp H) = H := by
  have hHu : IsUnit H.det := isUnit_det_of_posDef hH
  have hRu : IsUnit (fullBlockRefl d).det := isUnit_det_fullBlockRefl
  have hinv : (fullBlockRefl d * H⁻¹ * fullBlockRefl d)⁻¹ =
      fullBlockRefl d * H * fullBlockRefl d := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, fullBlockRefl_inv,
      Matrix.nonsing_inv_nonsing_inv _ hHu]
    noncomm_ring
  rw [fullBlockSharp, fullBlockSharp, hinv]
  calc fullBlockRefl d * (fullBlockRefl d * H * fullBlockRefl d) * fullBlockRefl d
      = (fullBlockRefl d * fullBlockRefl d) * H * (fullBlockRefl d * fullBlockRefl d) := by
        noncomm_ring
    _ = H := by rw [fullBlockRefl_mul_self, Matrix.one_mul, Matrix.mul_one]

/-- **The sharp map reverses the Loewner order**. -/
theorem fullBlockSharp_le_fullBlockSharp {H K : FullBlockMat d} (hH : H.PosDef)
    (hK : K.PosDef) (h : H ≤ K) : fullBlockSharp K ≤ fullBlockSharp H :=
  refl_conj_le_refl_conj (inv_le_inv_of_le hH hK h)

/-- **The sharp map is homogeneous of degree minus one**. -/
theorem fullBlockSharp_smul {H : FullBlockMat d} (hH : H.PosDef) {c : ℝ}
    (hc : 0 < c) : fullBlockSharp (c • H) = c⁻¹ • fullBlockSharp H := by
  have hHu : IsUnit H.det := isUnit_det_of_posDef hH
  have hcinv : (c • H)⁻¹ = c⁻¹ • H⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hHu,
      mul_inv_cancel₀ hc.ne', one_smul]
  rw [fullBlockSharp, fullBlockSharp, hcinv, Matrix.mul_smul, Matrix.smul_mul]

/-- The determinant of the sharp is the inverse determinant. -/
theorem det_fullBlockSharp {H : FullBlockMat d} (hH : H.PosDef) :
    (fullBlockSharp H).det = (H.det)⁻¹ := by
  have hHu : IsUnit H.det := isUnit_det_of_posDef hH
  have hR : (fullBlockRefl d).det * (fullBlockRefl d).det = 1 := by
    rw [← Matrix.det_mul, fullBlockRefl_mul_self, Matrix.det_one]
  rw [fullBlockSharp, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv']
  calc (fullBlockRefl d).det * (H.det)⁻¹ * (fullBlockRefl d).det
      = ((fullBlockRefl d).det * (fullBlockRefl d).det) * (H.det)⁻¹ := by ring
    _ = (H.det)⁻¹ := by rw [hR, one_mul]

/-! ## The shear and recentering -/

@[simp] theorem fullBlockShear_zero : fullBlockShear (0 : Mat d) = 1 := by
  rw [fullBlockShear, Matrix.fromBlocks_one]

theorem fullBlockShear_mul (h k : Mat d) :
    fullBlockShear h * fullBlockShear k = fullBlockShear (h + k) := by
  rw [fullBlockShear, fullBlockShear, fullBlockShear, Matrix.fromBlocks_multiply]
  simp

theorem fullBlockShear_inv (h : Mat d) :
    (fullBlockShear h)⁻¹ = fullBlockShear (-h) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [fullBlockShear_mul, add_neg_cancel, fullBlockShear_zero]

theorem isUnit_fullBlockShear (h : Mat d) : IsUnit (fullBlockShear h) :=
  ⟨⟨fullBlockShear h, fullBlockShear (-h),
      by rw [fullBlockShear_mul, add_neg_cancel, fullBlockShear_zero],
      by rw [fullBlockShear_mul, neg_add_cancel, fullBlockShear_zero]⟩, rfl⟩

theorem conjTranspose_fullBlockShear (h : Mat d) :
    (fullBlockShear h)ᴴ = Matrix.fromBlocks 1 (hᴴ) 0 1 := by
  rw [fullBlockShear, Matrix.fromBlocks_conjTranspose]
  simp

/-- The first recentering identity of the reference proof, `R G_h^{-1} = G_h^t R`,
for a skew `h`. -/
theorem refl_mul_shear_inv {h : Mat d} (hskew : hᴴ = -h) :
    fullBlockRefl d * (fullBlockShear h)⁻¹ = (fullBlockShear h)ᴴ * fullBlockRefl d := by
  rw [fullBlockShear_inv, fullBlockShear, fullBlockRefl, conjTranspose_fullBlockShear,
    hskew, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- The inverse of the transposed shear along a skew matrix is the transposed
shear along its negative. -/
theorem conjTranspose_fullBlockShear_inv {h : Mat d} (hskew : hᴴ = -h) :
    ((fullBlockShear h)ᴴ)⁻¹ = Matrix.fromBlocks 1 h 0 1 := by
  rw [conjTranspose_fullBlockShear, hskew]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.fromBlocks_multiply]
  simp

/-- The second recentering identity of the reference proof, `G_h^{-t} R = R G_h`,
for a skew `h`. -/
theorem shear_inv_conjTranspose_mul_refl {h : Mat d} (hskew : hᴴ = -h) :
    ((fullBlockShear h)ᴴ)⁻¹ * fullBlockRefl d = fullBlockRefl d * fullBlockShear h := by
  rw [conjTranspose_fullBlockShear_inv hskew, fullBlockRefl, fullBlockShear,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- **Recentering**: the sharp map commutes with congruence by a shear along a
skew matrix. -/
theorem fullBlockSharp_shear_conj {H : FullBlockMat d} (hH : H.PosDef)
    {h : Mat d} (hskew : hᴴ = -h) :
    fullBlockSharp ((fullBlockShear h)ᴴ * H * fullBlockShear h) =
      (fullBlockShear h)ᴴ * fullBlockSharp H * fullBlockShear h := by
  have hHu : IsUnit H.det := isUnit_det_of_posDef hH
  have hGdet : IsUnit (fullBlockShear h).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_fullBlockShear h)
  have hGHdet : IsUnit ((fullBlockShear h)ᴴ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp ((isUnit_fullBlockShear h).star)
  have hinv : ((fullBlockShear h)ᴴ * H * fullBlockShear h)⁻¹ =
      (fullBlockShear h)⁻¹ * H⁻¹ * ((fullBlockShear h)ᴴ)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    noncomm_ring
  rw [fullBlockSharp, fullBlockSharp, hinv]
  calc fullBlockRefl d * ((fullBlockShear h)⁻¹ * H⁻¹ * ((fullBlockShear h)ᴴ)⁻¹) *
        fullBlockRefl d
      = (fullBlockRefl d * (fullBlockShear h)⁻¹) * H⁻¹ *
          (((fullBlockShear h)ᴴ)⁻¹ * fullBlockRefl d) := by noncomm_ring
    _ = ((fullBlockShear h)ᴴ * fullBlockRefl d) * H⁻¹ *
          (fullBlockRefl d * fullBlockShear h) := by
        rw [refl_mul_shear_inv hskew, shear_inv_conjTranspose_mul_refl hskew]
    _ = (fullBlockShear h)ᴴ * (fullBlockRefl d * H⁻¹ * fullBlockRefl d) *
          fullBlockShear h := by noncomm_ring

end

end HighContrast
end HCPolySupport
