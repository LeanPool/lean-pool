/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.TransportObjects
public import LeanPool.HighContrastHomogenization.Geometry.DetOrder
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment

/-!
# High-contrast homogenization: Provider.Transport.BridgeAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The algebra of the bridge congruence

`p.two.grid.transport` compares the terminal annealed block of the
old grid with the terminal annealed block of the new one through the near
isometry `(1 - η_x)H ≤ F ≤ (1 + η_x)H`, and reads that comparison through the
congruence `S = H^{1/2}F^{-1/2}`.  Two displays record what the comparison says
about `S`: the normalization bounds `e.two.grid.inverse.comparison`
and the determinant bounds `e.two.grid.determinant`.

Both are proved here, in the generality in which the transport proof uses them:
`H` and `F` are arbitrary positive definite doubled blocks.  The first step is
the identity `S^tS = F^{-1/2}HF^{-1/2}`, which says that the Gram matrix of the
bridge is the normalization of the old terminal block by the new one; after
that, the first display is the comparison conjugated by `F^{-1/2}`, and the
second is the comparison with determinants taken.

The determinant display carries the only arithmetic in the paragraph.  The
matrices have size `2d` while the determinant root uses the `d`-th root, so a
scalar dilation by `c` multiplies the determinant by `c^{2d}` and the root by
`c^2`; that is where the squares in `(1 - η_x)^2` and `(1 + η_x)^2` come from.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The Gram matrix of the bridge is a normalization -/

/-- The flattened Gram matrix of the bridge congruence is the literal
congruence `F^{-1/2}HF^{-1/2}`: the two inner square roots of `H` multiply to
`H`, and both square roots are symmetric. -/
theorem toFullBlockMat_bridgeGram {H F : BlockMat d}
    (hH : (toFullBlockMat H).PosSemidef) (hF : (toFullBlockMat F).PosDef) :
    toFullBlockMat (bridgeGram H F) =
      matSqrt (toFullBlockMat F)⁻¹ * toFullBlockMat H * matSqrt (toFullBlockMat F)⁻¹ := by
  have hsqH : (matSqrt (toFullBlockMat H))ᵀ = matSqrt (toFullBlockMat H) := by
    rw [← conjTranspose_eq_transpose']
    exact (matSqrt_spec hH).1.isHermitian
  have hsqF : (matSqrt ((toFullBlockMat F)⁻¹))ᵀ = matSqrt ((toFullBlockMat F)⁻¹) :=
    transpose_matSqrt_inv hF
  rw [bridgeGram, toFullBlockMat_ofFullBlockMat, bridgeMap, Matrix.transpose_mul, hsqH,
    hsqF]
  calc
    matSqrt ((toFullBlockMat F)⁻¹) * matSqrt (toFullBlockMat H) *
        (matSqrt (toFullBlockMat H) * matSqrt ((toFullBlockMat F)⁻¹))
        = matSqrt ((toFullBlockMat F)⁻¹) *
            (matSqrt (toFullBlockMat H) * matSqrt (toFullBlockMat H)) *
            matSqrt ((toFullBlockMat F)⁻¹) := by
          noncomm_ring
    _ = matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat H *
          matSqrt ((toFullBlockMat F)⁻¹) := by
          rw [(matSqrt_spec hH).2]

/-- The Gram matrix of a bridge between positive definite blocks is positive
definite. -/
theorem posDef_toFullBlockMat_bridgeGram {H F : BlockMat d}
    (hH : (toFullBlockMat H).PosDef) (hF : (toFullBlockMat F).PosDef) :
    (toFullBlockMat (bridgeGram H F)).PosDef := by
  rw [toFullBlockMat_bridgeGram hH.posSemidef hF]
  exact posDef_normalize hH hF

/-- The Gram matrix of a bridge between positive definite blocks is symmetric. -/
theorem isSymmetricBlockMat_bridgeGram {H F : BlockMat d}
    (hH : (toFullBlockMat H).PosDef) (hF : (toFullBlockMat F).PosDef) :
    IsSymmetricBlockMat (bridgeGram H F) :=
  isSymmetricBlockMat_of_posSemidef (posDef_toFullBlockMat_bridgeGram hH hF).posSemidef

/-! ## The normalization display -/

/-- A scalar dilation of the identity is monotone in the scalar. -/
private theorem smul_one_le_smul_one {c c' : ℝ} (h : c ≤ c') :
    c • (1 : FullBlockMat d) ≤ c' • (1 : FullBlockMat d) := by
  refine Matrix.le_iff.mpr ?_
  have hrw : c' • (1 : FullBlockMat d) - c • 1 = (c' - c) • (1 : FullBlockMat d) := by
    rw [sub_smul]
  rw [hrw]
  exact (Matrix.PosSemidef.one).smul (sub_nonneg.mpr h)

/-- The upper half of the normalization display, on the flattened carrier: the
lower near-isometric bound conjugated by `F^{-1/2}` gives `S^tS ≤ (1-η_x)^{-1}I`.
-/
private theorem toFullBlockMat_bridgeGram_le {H F : BlockMat d}
    (hH : (toFullBlockMat H).PosDef) (hF : (toFullBlockMat F).PosDef) {etaX : ℝ}
    (hlt : etaX < 1)
    (hlo : ((1 - etaX) • toFullBlockMat H) ≤ toFullBlockMat F) :
    toFullBlockMat (bridgeGram H F) ≤ (1 - etaX)⁻¹ • (1 : FullBlockMat d) := by
  have hpos : 0 < 1 - etaX := by linarith only [hlt]
  have hcong := conj_le_conj' (conjTranspose_matSqrt_inv hF) hlo
  rw [matSqrt_inv_conj hF] at hcong
  have hrw : matSqrt ((toFullBlockMat F)⁻¹) * ((1 - etaX) • toFullBlockMat H) *
      matSqrt ((toFullBlockMat F)⁻¹) =
      (1 - etaX) • toFullBlockMat (bridgeGram H F) := by
    rw [toFullBlockMat_bridgeGram hH.posSemidef hF, Matrix.mul_smul, Matrix.smul_mul]
  rw [hrw] at hcong
  have hscaled := smul_le_smul_of_le (inv_nonneg.mpr hpos.le) hcong
  rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul] at hscaled
  exact hscaled

/-- The lower half of the normalization display, on the flattened carrier: the
upper near-isometric bound conjugated by `F^{-1/2}` gives `(1+η_x)^{-1}I ≤ S^tS`.
-/
private theorem le_toFullBlockMat_bridgeGram {H F : BlockMat d}
    (hH : (toFullBlockMat H).PosDef) (hF : (toFullBlockMat F).PosDef) {etaX : ℝ}
    (hetaX : 0 ≤ etaX)
    (hhi : toFullBlockMat F ≤ ((1 + etaX) • toFullBlockMat H)) :
    (1 + etaX)⁻¹ • (1 : FullBlockMat d) ≤ toFullBlockMat (bridgeGram H F) := by
  have hpos : 0 < 1 + etaX := by linarith only [hetaX]
  have hcong := conj_le_conj' (conjTranspose_matSqrt_inv hF) hhi
  rw [matSqrt_inv_conj hF] at hcong
  have hrw : matSqrt ((toFullBlockMat F)⁻¹) * ((1 + etaX) • toFullBlockMat H) *
      matSqrt ((toFullBlockMat F)⁻¹) =
      (1 + etaX) • toFullBlockMat (bridgeGram H F) := by
    rw [toFullBlockMat_bridgeGram hH.posSemidef hF, Matrix.mul_smul, Matrix.smul_mul]
  rw [hrw] at hcong
  have hscaled := smul_le_smul_of_le (inv_nonneg.mpr hpos.le) hcong
  rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul] at hscaled
  exact hscaled

/-- **The bridge normalization display** (`e.two.grid.inverse.comparison`).
For a near isometry `(1 - η_x)H ≤ F ≤ (1 + η_x)H` with `0 ≤ η_x ≤ 1/4`, the Gram
matrix of the bridge congruence `S = H^{1/2}F^{-1/2}` satisfies both printed
pairs of bounds: the first pair is the comparison conjugated by `F^{-1/2}`, and
the second follows from it, the upper bound being an identity of scalars and the
lower one the inequality `2η_x^2 ≥ 0`. -/
theorem bridge_normalization {H F : BlockMat d}
    (hH : (toFullBlockMat H).PosDef) (hF : (toFullBlockMat F).PosDef) {etaX : ℝ}
    (hetaX : 0 ≤ etaX) (hetaX4 : etaX ≤ 1 / 4)
    (hlo : BlockMatLoewnerLE (blockScale (1 - etaX) H) F)
    (hhi : BlockMatLoewnerLE F (blockScale (1 + etaX) H)) :
    BlockMatLoewnerLE (blockScale (1 + etaX)⁻¹ (Book.Ch02.blockIdentity d))
        (bridgeGram H F) ∧
      BlockMatLoewnerLE (bridgeGram H F)
        (blockScale (1 - etaX)⁻¹ (Book.Ch02.blockIdentity d)) ∧
      BlockMatLoewnerLE (blockScale (1 - etaX / (1 - etaX)) (Book.Ch02.blockIdentity d))
        (bridgeGram H F) ∧
      BlockMatLoewnerLE (bridgeGram H F)
        (blockScale (1 + etaX / (1 - etaX)) (Book.Ch02.blockIdentity d)) := by
  have hsymmH : IsSymmetricBlockMat H := isSymmetricBlockMat_of_posSemidef hH.posSemidef
  have hsymmF : IsSymmetricBlockMat F := isSymmetricBlockMat_of_posSemidef hF.posSemidef
  have hlt : etaX < 1 := by linarith only [hetaX4]
  have hpos : 0 < 1 - etaX := by linarith only [hlt]
  have hpos' : 0 < 1 + etaX := by linarith only [hetaX]
  have hloFull : ((1 - etaX) • toFullBlockMat H) ≤ toFullBlockMat F := by
    have := le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockScale _ hsymmH) hsymmF hlo
    rwa [toFullBlockMat_blockScale] at this
  have hhiFull : toFullBlockMat F ≤ ((1 + etaX) • toFullBlockMat H) := by
    have := le_of_blockMatLoewnerLE hsymmF (isSymmetricBlockMat_blockScale _ hsymmH) hhi
    rwa [toFullBlockMat_blockScale] at this
  have hupper := toFullBlockMat_bridgeGram_le hH hF hlt hloFull
  have hlower := le_toFullBlockMat_bridgeGram hH hF hetaX hhiFull
  -- the two scalar comparisons of the second printed pair
  have hne : (1 : ℝ) - etaX ≠ 0 := hpos.ne'
  have hne' : (1 : ℝ) + etaX ≠ 0 := hpos'.ne'
  have hid : 1 + etaX / (1 - etaX) = (1 - etaX)⁻¹ := by
    field_simp
    ring
  have hcmp : 1 - etaX / (1 - etaX) ≤ (1 + etaX)⁻¹ := by
    have hkey : (1 + etaX)⁻¹ - (1 - etaX / (1 - etaX)) =
        2 * etaX ^ 2 / ((1 - etaX) * (1 + etaX)) := by
      field_simp
      ring
    have hnn : 0 ≤ 2 * etaX ^ 2 / ((1 - etaX) * (1 + etaX)) :=
      div_nonneg (by positivity) (mul_pos hpos hpos').le
    rw [← hkey] at hnn
    linarith only [hnn]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, toFullBlockMat_blockIdentity]
    exact hlower
  · refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, toFullBlockMat_blockIdentity]
    exact hupper
  · refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, toFullBlockMat_blockIdentity]
    exact (smul_one_le_smul_one hcmp).trans hlower
  · refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, toFullBlockMat_blockIdentity, hid]
    exact hupper

/-! ## The determinant display -/

/-- The `d`-th root of the `2d`-th power of a nonnegative scalar is its square.
This is the arithmetic behind the squares in the determinant display: a
dilation of a `2d`-by-`2d` matrix by `c` multiplies its determinant by `c^{2d}`,
and the determinant root takes the `d`-th root. -/
private theorem rpow_inv_pow_two_mul {c : ℝ} (hc : 0 ≤ c) {d : ℕ} (hd : d ≠ 0) :
    (c ^ (2 * d)) ^ ((d : ℝ)⁻¹) = c ^ 2 := by
  rw [← Real.rpow_natCast c (2 * d), ← Real.rpow_mul hc]
  have hrw : ((2 * d : ℕ) : ℝ) * (d : ℝ)⁻¹ = 2 := by
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    push_cast
    field_simp
  rw [hrw, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- One side of the determinant display, in the form both sides use: a scalar
dilation below a positive definite block passes to the determinant roots with
the scalar squared. -/
private theorem detRoot_le_of_smul_le {A B : FullBlockMat d} (hA : A.PosDef) (hB : B.PosDef)
    (hd : d ≠ 0) {c : ℝ} (hc : 0 < c) (h : (c • A) ≤ B) :
    c ^ 2 * A.det ^ ((d : ℝ)⁻¹) ≤ B.det ^ ((d : ℝ)⁻¹) := by
  have hdet := det_le_det_of_le (hA.smul hc) hB h
  rw [Matrix.det_smul, show Fintype.card (BlockCoord d) = 2 * d by
    simp [Fintype.card_sum, two_mul]] at hdet
  have hcpow : (0 : ℝ) ≤ c ^ (2 * d) := pow_nonneg hc.le _
  have hmono := Real.rpow_le_rpow (mul_nonneg hcpow hA.det_pos.le) hdet
    (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
  rwa [Real.mul_rpow hcpow hA.det_pos.le, rpow_inv_pow_two_mul hc.le hd] at hmono

/-- **The bridge determinant display** (`e.two.grid.determinant`).
Taking determinants in the near isometry `(1 - η_x)H ≤ F ≤ (1 + η_x)H` and
recalling that the blocks have size `2d` while the determinant root uses the
`d`-th root gives the two printed bounds, with the bridge error squared. -/
theorem bridge_determinant {H F : BlockMat d} (hd : d ≠ 0)
    (hH : (toFullBlockMat H).PosDef) (hF : (toFullBlockMat F).PosDef) {etaX : ℝ}
    (hetaX : 0 ≤ etaX) (hetaX4 : etaX ≤ 1 / 4)
    (hlo : BlockMatLoewnerLE (blockScale (1 - etaX) H) F)
    (hhi : BlockMatLoewnerLE F (blockScale (1 + etaX) H)) :
    (1 - etaX) ^ 2 * detRoot d H ≤ detRoot d F ∧
      detRoot d F ≤ (1 + etaX) ^ 2 * detRoot d H := by
  have hsymmH : IsSymmetricBlockMat H := isSymmetricBlockMat_of_posSemidef hH.posSemidef
  have hsymmF : IsSymmetricBlockMat F := isSymmetricBlockMat_of_posSemidef hF.posSemidef
  have hpos : 0 < 1 - etaX := by linarith only [hetaX4]
  have hpos' : 0 < 1 + etaX := by linarith only [hetaX]
  have hloFull : ((1 - etaX) • toFullBlockMat H) ≤ toFullBlockMat F := by
    have := le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockScale _ hsymmH) hsymmF hlo
    rwa [toFullBlockMat_blockScale] at this
  have hhiFull : toFullBlockMat F ≤ ((1 + etaX) • toFullBlockMat H) := by
    have := le_of_blockMatLoewnerLE hsymmF (isSymmetricBlockMat_blockScale _ hsymmH) hhi
    rwa [toFullBlockMat_blockScale] at this
  refine ⟨detRoot_le_of_smul_le hH hF hd hpos hloFull, ?_⟩
  -- the upper bound is the lower one applied to the reversed comparison, after
  -- dividing the dilated block back
  have hscaled : ((1 + etaX)⁻¹ • toFullBlockMat F) ≤ toFullBlockMat H := by
    have := smul_le_smul_of_le (inv_nonneg.mpr hpos'.le) hhiFull
    rwa [smul_smul, inv_mul_cancel₀ hpos'.ne', one_smul] at this
  have hstep := detRoot_le_of_smul_le hF hH hd (inv_pos.mpr hpos') hscaled
  have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ (1 + etaX) ^ 2)
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hpos'.ne', one_pow, one_mul] at hmul
  exact hmul

end

end Transport
end HighContrast
end HCPolySupport
