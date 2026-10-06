/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.Sharp
public import LeanPool.HighContrastHomogenization.Setup.Moments

/-!
# High-contrast homogenization: Geometry.BlockBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bridge between the two block dialects

A doubled block matrix is carried in two equivalent ways.  The structural
carrier `BlockMat d` records the four `d × d` corners separately and comes with
its own multiplication, transpose, inverse, dilation, reflection, quadratic-form
order `BlockMatLoewnerLE`, and positivity predicate `BlockPosDef`.  The
flattened carrier `FullBlockMat d = Matrix (BlockCoord d) (BlockCoord d) ℝ` is a
genuine matrix ring over the doubled index type, so it carries mathlib's
multiplication, inverse, Loewner order, `PosDef`, and square root; the canonical
block geometry of `e.scale.selection.canonical.metric` is developed there.

This file shows that the flattening map `toFullBlockMat` identifies the two:
it is a ring isomorphism onto `FullBlockMat d` sending each structural operation
to its matrix counterpart, and — on symmetric data — it identifies
`BlockMatLoewnerLE` with the Loewner order and `BlockPosDef` with `PosDef`.

Symmetry is needed for one direction only.  A Loewner inequality between
flattened matrices always implies the corresponding inequality of quadratic
forms; the converse needs the difference to be Hermitian, which for real data is
exactly the symmetry of the two blocks.  This asymmetry is recorded in the two
one-directional lemmas, and `blockMatLoewnerLE_iff_le` assumes symmetry of both
arguments.

The final section transports the primal-adjoint involution `H^♯ = R H^{-1} R`,
formed with the swap matrix `R` of `s.scale.selection`.  The structural
`blockSharp` and the flattened `fullBlockSharp` correspond under the bridge with
no hypotheses at all, so its rules — involution, order reversal, homogeneity of
degree minus one — become available in the structural dialect by transport.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## Structure transport

`toFullBlockMat` is the map that assembles the four corners into one matrix over
the doubled index type; it is mathlib's `Matrix.fromBlocks`. -/

/-- The flattening map is `Matrix.fromBlocks` on the four corners. -/
theorem toFullBlockMat_eq_fromBlocks (A : BlockMat d) :
    toFullBlockMat A =
      Matrix.fromBlocks A.upperLeft A.upperRight A.lowerLeft A.lowerRight := by
  ext α β
  cases α <;> cases β <;> rfl

/-- The flattening map is injective; `ofFullBlockMat` is its inverse. -/
theorem toFullBlockMat_injective :
    Function.Injective (toFullBlockMat (d := d)) := by
  intro A B h
  rw [← ofFullBlockMat_toFullBlockMat A, ← ofFullBlockMat_toFullBlockMat B, h]

/-- Flattening turns the structural product into the matrix product. -/
theorem toFullBlockMat_blockMatMul (A B : BlockMat d) :
    toFullBlockMat (Book.Ch02.blockMatMul A B) =
      toFullBlockMat A * toFullBlockMat B := by
  rw [toFullBlockMat_eq_fromBlocks, toFullBlockMat_eq_fromBlocks,
    toFullBlockMat_eq_fromBlocks, Matrix.fromBlocks_multiply]
  rfl

/-- Flattening turns the structural block diagonal into `Matrix.fromBlocks`. -/
theorem toFullBlockMat_blockDiag (A B : Mat d) :
    toFullBlockMat (Book.Ch02.blockDiag A B) = Matrix.fromBlocks A 0 0 B :=
  toFullBlockMat_eq_fromBlocks _

/-- Flattening turns the structural identity into the matrix identity. -/
theorem toFullBlockMat_blockIdentity :
    toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
  rw [Book.Ch02.blockIdentity, toFullBlockMat_blockDiag, Matrix.fromBlocks_one]

/-- Flattening turns the structural transpose into the matrix transpose. -/
theorem toFullBlockMat_blockMatTranspose (A : BlockMat d) :
    toFullBlockMat (Book.Ch02.blockMatTranspose A) = (toFullBlockMat A)ᵀ := by
  rw [toFullBlockMat_eq_fromBlocks, toFullBlockMat_eq_fromBlocks,
    Matrix.fromBlocks_transpose]
  rfl

/-- Over the reals the structural transpose is the conjugate transpose of the
flattened matrix. -/
theorem toFullBlockMat_blockMatTranspose_conj (A : BlockMat d) :
    toFullBlockMat (Book.Ch02.blockMatTranspose A) = (toFullBlockMat A)ᴴ := by
  rw [toFullBlockMat_blockMatTranspose, conjTranspose_eq_transpose']

/-- Flattening turns the structural inverse into the matrix inverse.  The
structural inverse is defined by flattening, inverting and unflattening, so this
is the round trip. -/
theorem toFullBlockMat_blockMatInv (A : BlockMat d) :
    toFullBlockMat (Book.Ch02.blockMatInv A) = (toFullBlockMat A)⁻¹ := by
  rw [Book.Ch02.blockMatInv, toFullBlockMat_ofFullBlockMat]

/-- Flattening turns the structural dilation into the scalar action. -/
theorem toFullBlockMat_blockScale (c : ℝ) (A : BlockMat d) :
    toFullBlockMat (blockScale c A) = c • toFullBlockMat A := by
  rw [toFullBlockMat_eq_fromBlocks, toFullBlockMat_eq_fromBlocks,
    Matrix.fromBlocks_smul]
  rfl

/-- Flattening turns the structural reflection matrix `R` into `fullBlockRefl`. -/
theorem toFullBlockMat_blockR :
    toFullBlockMat (Book.Ch02.blockR d) = fullBlockRefl d :=
  toFullBlockMat_eq_fromBlocks _

/-- Flattening turns the structural shear `G_h` into `fullBlockShear`. -/
theorem toFullBlockMat_blockG (h : Mat d) :
    toFullBlockMat (Book.Ch02.blockG h) = fullBlockShear h :=
  toFullBlockMat_eq_fromBlocks _

/-- Flattening turns the structural corner swap into conjugation by `R`. -/
theorem toFullBlockMat_blockReflect (A : BlockMat d) :
    toFullBlockMat (blockReflect A) =
      fullBlockRefl d * toFullBlockMat A * fullBlockRefl d := by
  rw [toFullBlockMat_eq_fromBlocks, toFullBlockMat_eq_fromBlocks, fullBlockRefl,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [blockReflect]

/-! ## Symmetry and the quadratic form -/

/-- The structural entry function is the entry function of the flattened
matrix. -/
theorem blockMatEntry_eq_toFullBlockMat (A : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry A α β = toFullBlockMat A α β := by
  cases α <;> cases β <;> rfl

/-- Structural symmetry is symmetry of the flattened matrix. -/
theorem isSymm_toFullBlockMat {A : BlockMat d} (hA : IsSymmetricBlockMat A) :
    (toFullBlockMat A).IsSymm := by
  rw [Matrix.IsSymm]
  ext α β
  simpa [blockMatEntry_eq_toFullBlockMat] using hA β α

/-- Structural symmetry makes the flattened matrix Hermitian. -/
theorem isHermitian_toFullBlockMat {A : BlockMat d} (hA : IsSymmetricBlockMat A) :
    (toFullBlockMat A).IsHermitian :=
  isHermitian_of_isSymm (isSymm_toFullBlockMat hA)

/-- The structural quadratic form is the flattened quadratic form. -/
theorem blockVecDot_blockMatVecMul_eq_dotProduct (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      toFullBlockVec X ⬝ᵥ toFullBlockMat A *ᵥ toFullBlockVec X := by
  rw [← dotProduct_toFullBlockVec X (blockMatVecMul A X),
    toFullBlockVec_blockMatVecMul]

/-- Flattening a doubled vector detects vanishing. -/
theorem toFullBlockVec_eq_zero_iff (X : BlockVec d) :
    toFullBlockVec X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have h' := congrArg ofFullBlockVec h
    rwa [ofFullBlockVec_toFullBlockVec] at h'
  · rintro rfl
    funext α
    cases α <;> rfl

/-! ## Order transport

Only the passage from the quadratic-form order to the Loewner order needs
symmetry, and it needs it on both arguments: the Loewner order is defined by
positive semidefiniteness of the difference, and a real matrix is positive
semidefinite only if it is symmetric. -/

/-- **The Loewner order implies the quadratic-form order.**  No symmetry
hypothesis is needed in this direction. -/
theorem blockMatLoewnerLE_of_le {A B : BlockMat d}
    (h : toFullBlockMat A ≤ toFullBlockMat B) : BlockMatLoewnerLE A B := by
  intro X
  have hPS : (toFullBlockMat B - toFullBlockMat A).PosSemidef := Matrix.le_iff.mp h
  have hx := hPS.dotProduct_mulVec_nonneg (toFullBlockVec X)
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  simp only [star_trivial] at hx
  rw [blockVecDot_blockMatVecMul_eq_dotProduct, blockVecDot_blockMatVecMul_eq_dotProduct]
  linarith only [hx]

/-- **The difference of two symmetric blocks is positive semidefinite** as soon
as the quadratic forms compare.  This is the intermediate through which the
order transport runs. -/
theorem posSemidef_toFullBlockMat_sub_of_blockMatLoewnerLE {A B : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B)
    (h : BlockMatLoewnerLE A B) :
    (toFullBlockMat B - toFullBlockMat A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((isHermitian_toFullBlockMat hB).sub (isHermitian_toFullBlockMat hA)) fun x => ?_
  have hX := h (ofFullBlockVec x)
  rw [blockVecDot_blockMatVecMul_eq_dotProduct, blockVecDot_blockMatVecMul_eq_dotProduct,
    toFullBlockVec_ofFullBlockVec] at hX
  rw [Matrix.sub_mulVec, dotProduct_sub]
  simp only [star_trivial]
  linarith only [hX]

/-- **The quadratic-form order implies the Loewner order**, for symmetric
blocks. -/
theorem le_of_blockMatLoewnerLE {A B : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B)
    (h : BlockMatLoewnerLE A B) : toFullBlockMat A ≤ toFullBlockMat B :=
  Matrix.le_iff.mpr (posSemidef_toFullBlockMat_sub_of_blockMatLoewnerLE hA hB h)

/-- **The two orders agree on symmetric blocks.** -/
theorem blockMatLoewnerLE_iff_le {A B : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B) :
    BlockMatLoewnerLE A B ↔ toFullBlockMat A ≤ toFullBlockMat B :=
  ⟨le_of_blockMatLoewnerLE hA hB, blockMatLoewnerLE_of_le⟩

/-- **The two positivity predicates agree on symmetric blocks.** -/
theorem blockPosDef_iff_posDef {A : BlockMat d} (hA : IsSymmetricBlockMat A) :
    Book.Ch02.BlockPosDef A ↔ (toFullBlockMat A).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · refine fun hpd => ⟨isHermitian_toFullBlockMat hA, fun x hx => ?_⟩
    have hne : ofFullBlockVec x ≠ 0 := by
      intro hzero
      exact hx (by rw [← toFullBlockVec_ofFullBlockVec x, hzero]; funext α; cases α <;> rfl)
    have hX := hpd (ofFullBlockVec x) hne
    rw [blockVecDot_blockMatVecMul_eq_dotProduct, toFullBlockVec_ofFullBlockVec] at hX
    simpa using hX
  · rintro ⟨-, hpos⟩ X hX
    have hne : toFullBlockVec X ≠ 0 := fun hzero => hX ((toFullBlockVec_eq_zero_iff X).mp hzero)
    have h := hpos hne
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simpa using h

/-- Positive definiteness of a symmetric block transports to the flattened
matrix. -/
theorem posDef_toFullBlockMat {A : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hpd : Book.Ch02.BlockPosDef A) : (toFullBlockMat A).PosDef :=
  (blockPosDef_iff_posDef hA).mp hpd

/-! ## The sharp involution

The structural sharp is the corner swap of the structural
inverse; flattening turns the corner swap into conjugation by `R` and the
structural inverse into the matrix inverse, so it agrees exactly with
`fullBlockSharp`. -/

/-- **The sharp map is the same on both carriers.** -/
theorem toFullBlockMat_blockSharp (H : BlockMat d) :
    toFullBlockMat (blockSharp H) = fullBlockSharp (toFullBlockMat H) := by
  rw [blockSharp, toFullBlockMat_blockReflect, toFullBlockMat_blockMatInv,
    fullBlockSharp]

/-- **The sharp map is an involution**, in the structural dialect. -/
theorem blockSharp_blockSharp {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hpd : Book.Ch02.BlockPosDef H) : blockSharp (blockSharp H) = H := by
  refine toFullBlockMat_injective ?_
  rw [toFullBlockMat_blockSharp, toFullBlockMat_blockSharp]
  exact fullBlockSharp_fullBlockSharp (posDef_toFullBlockMat hH hpd)

/-- **The sharp map reverses the order**, in the structural dialect. -/
theorem blockMatLoewnerLE_blockSharp_of_le {H K : BlockMat d}
    (hH : IsSymmetricBlockMat H) (hK : IsSymmetricBlockMat K)
    (hHpd : Book.Ch02.BlockPosDef H) (hKpd : Book.Ch02.BlockPosDef K)
    (h : BlockMatLoewnerLE H K) : BlockMatLoewnerLE (blockSharp K) (blockSharp H) := by
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockSharp, toFullBlockMat_blockSharp]
  exact fullBlockSharp_le_fullBlockSharp (posDef_toFullBlockMat hH hHpd)
    (posDef_toFullBlockMat hK hKpd) (le_of_blockMatLoewnerLE hH hK h)

/-- **The sharp map is homogeneous of degree minus one**, in the structural
dialect. -/
theorem blockSharp_blockScale {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hpd : Book.Ch02.BlockPosDef H) {c : ℝ} (hc : 0 < c) :
    blockSharp (blockScale c H) = blockScale c⁻¹ (blockSharp H) := by
  refine toFullBlockMat_injective ?_
  simp only [toFullBlockMat_blockSharp, toFullBlockMat_blockScale]
  exact fullBlockSharp_smul (posDef_toFullBlockMat hH hpd) hc

end

end HighContrast
end HCPolySupport
