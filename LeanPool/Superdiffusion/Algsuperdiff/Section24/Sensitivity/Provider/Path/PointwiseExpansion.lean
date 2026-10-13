/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.Structures

/-!
# PointwiseExpansion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Pointwise second-difference expansion of the doubled coefficient matrix

The proof of `l.sensitivity.coarse.grained.general` rests on the pointwise
algebra `e.bfA.LDLt` + `e.Gh.additive`: perturbing the coefficient matrix `A`
by a skew matrix `g` conjugates the doubled matrix `bfA` by the shear
`G_{-g}`, because the symmetric part is unchanged and the skew part is
translated.  At the level of quadratic forms this conjugation is *exactly*
quadratic in the perturbation:

`X · bfA(A + g) X = X · bfA(A) X - 2 (g X₁) · (bfA(A) X)₂ + (g X₁) · s⁻¹ (g X₁)`

with `s := symmPart A`.  This identity is pure matrix algebra: it never
inverts `s`, so it holds for the Mathlib junk-value inverse as well.  It is
the entire second-difference content of the upper *and* lower coarse-matrix
expansions; everything downstream is integration and minimizer bookkeeping.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open HCPolySupport HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The symmetric part is additive. -/
theorem symmPart_add (A B : Mat d) :
    symmPart (A + B) = symmPart A + symmPart B := by
  ext i j
  simp only [symmPart, Matrix.add_apply]
  ring

/-- The skew part is additive. -/
theorem skewPart_add (A B : Mat d) :
    skewPart (A + B) = skewPart A + skewPart B := by
  ext i j
  simp only [skewPart, Matrix.add_apply]
  ring

/-- The symmetric part of a scalar multiple. -/
theorem symmPart_smul (c : ℝ) (A : Mat d) :
    symmPart (c • A) = c • symmPart A := by
  ext i j
  simp only [symmPart, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A matrix with vanishing symmetric part is its own skew part. -/
theorem skewPart_eq_self_of_symmPart_eq_zero {g : Mat d}
    (hg : symmPart g = 0) : skewPart g = g := by
  ext i j
  have h := congrFun (congrFun hg i) j
  simp only [symmPart, Matrix.zero_apply] at h
  simp only [skewPart]
  linarith

/-- The symmetric part is a symmetric matrix. -/
theorem isSymm_symmPart (A : Mat d) : (symmPart A).IsSymm := by
  show (symmPart A).transpose = symmPart A
  simpa [matTranspose] using matTranspose_symmPart A

/-- A matrix with vanishing symmetric part is antisymmetric. -/
theorem matTranspose_eq_neg_self_of_symmPart_eq_zero {g : Mat d}
    (hg : symmPart g = 0) : matTranspose g = -g := by
  ext i j
  have h := congrFun (congrFun hg j) i
  simp only [symmPart, Matrix.zero_apply] at h
  simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply]
  linarith

/-- The quadratic form of a matrix with vanishing symmetric part vanishes. -/
theorem vecDot_matVecMul_self_eq_zero_of_symmPart_eq_zero {g : Mat d}
    (hg : symmPart g = 0) (ξ : Vec d) :
    vecDot ξ (matVecMul g ξ) = 0 := by
  rw [← vecDot_matVecMul_symmPart, hg,
    show matVecMul (0 : Mat d) ξ = 0 by
      funext i
      show (∑ j : Fin d, (0 : ℝ) * ξ j) = 0
      simp,
    vecDot_zero_right]

/-- The bilinear pairing of a matrix with vanishing symmetric part is
antisymmetric. -/
theorem vecDot_matVecMul_antisymm_of_symmPart_eq_zero {g : Mat d}
    (hg : symmPart g = 0) (u v : Vec d) :
    vecDot u (matVecMul g v) = -vecDot v (matVecMul g u) := by
  have h := vecDot_matVecMul_transpose v u g
  rw [matTranspose_eq_neg_self_of_symmPart_eq_zero hg, neg_matVecMul,
    vecDot_neg_right] at h
  rw [vecDot_comm u (matVecMul g v), ← h]

/-- The Chapter 2 doubled matrix field is the pointwise doubled matrix of the
coefficient representative. -/
theorem blockMatrixField_eq_blockMatrixOfCoeff {U : Domain d}
    (a : CoeffOn U) (x : Vec d) :
    blockMatrixField a x = blockMatrixOfCoeff (a.toCoeffField x) :=
  rfl

/-- Second component of `bfA(A) X`, in the canonical `s⁻¹ (k X₁ - X₂)` form. -/
theorem blockMatVecMul_blockMatrixOfCoeff_snd (A : Mat d) (X : BlockVec d) :
    (blockMatVecMul (blockMatrixOfCoeff A) X).2 =
      -(matVecMul (symmPart A)⁻¹
        (matVecMul (skewPart A) X.1 - X.2)) := by
  show matVecMul (-((symmPart A)⁻¹ * skewPart A)) X.1 +
      matVecMul (symmPart A)⁻¹ X.2 = _
  rw [neg_matVecMul, ← matVecMul_mul, sub_eq_add_neg,
    matVecMul_add, matVecMul_neg]
  abel

/-- First component of `bfA(A) X`, expressed through the second component. -/
theorem blockMatVecMul_blockMatrixOfCoeff_fst (A : Mat d) (X : BlockVec d) :
    (blockMatVecMul (blockMatrixOfCoeff A) X).1 =
      matVecMul (symmPart A) X.1 +
        matVecMul (skewPart A)
          ((blockMatVecMul (blockMatrixOfCoeff A) X).2) := by
  rw [blockMatVecMul_blockMatrixOfCoeff_snd]
  show matVecMul (symmPart A + matTranspose (skewPart A) * (symmPart A)⁻¹ *
        skewPart A) X.1 +
      matVecMul (-(matTranspose (skewPart A) * (symmPart A)⁻¹)) X.2 = _
  have htk : matTranspose (skewPart A) = -skewPart A := by
    ext i j
    simp [matTranspose, skewPart]
    ring
  rw [htk]
  simp only [Matrix.neg_mul, Matrix.mul_assoc, add_matVecMul, neg_matVecMul,
    ← matVecMul_mul, sub_eq_add_neg, matVecMul_add, matVecMul_neg, neg_neg]
  abel

/-- The canonical form `X·bfA(A)X = X₁·sX₁ + (kX₁ - X₂)·s⁻¹(kX₁ - X₂)` of the
doubled quadratic form.  No invertibility of `s` is used. -/
theorem blockQuadForm_blockMatrixOfCoeff (A : Mat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) =
      vecDot X.1 (matVecMul (symmPart A) X.1) +
        vecDot (matVecMul (skewPart A) X.1 - X.2)
          (matVecMul (symmPart A)⁻¹
            (matVecMul (skewPart A) X.1 - X.2)) := by
  set s := symmPart A with hs
  set k := skewPart A with hk
  show vecDot X.1
        (matVecMul (s + matTranspose k * s⁻¹ * k) X.1 +
          matVecMul (-(matTranspose k * s⁻¹)) X.2) +
      vecDot X.2
        (matVecMul (-(s⁻¹ * k)) X.1 + matVecMul s⁻¹ X.2) = _
  rw [add_matVecMul, neg_matVecMul, neg_matVecMul]
  rw [show matTranspose k * s⁻¹ * k = matTranspose k * (s⁻¹ * k) by
    rw [Matrix.mul_assoc]]
  rw [← matVecMul_mul (matTranspose k), ← matVecMul_mul s⁻¹ k,
    ← matVecMul_mul (matTranspose k) s⁻¹]
  rw [vecDot_add_right, vecDot_add_right, vecDot_add_right,
    vecDot_neg_right, vecDot_neg_right,
    vecDot_matVecMul_transpose, vecDot_matVecMul_transpose]
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg,
    vecDot_add_left, vecDot_neg_left,
    vecDot_add_right, vecDot_add_right,
    vecDot_neg_right, vecDot_neg_right]
  ring

/-- The second component of `bfA X` flips sign under simultaneous transpose of
the coefficient matrix and flux flip of the doubled vector. -/
theorem blockMatVecMul_blockMatrixOfCoeff_transpose_fluxFlip_snd
    (A : Mat d) (X : BlockVec d) :
    (blockMatVecMul (blockMatrixOfCoeff (matTranspose A)) (X.1, -X.2)).2 =
      -(blockMatVecMul (blockMatrixOfCoeff A) X).2 := by
  rw [blockMatVecMul_blockMatrixOfCoeff_snd (matTranspose A)
      ((X.1, -X.2) : BlockVec d),
    blockMatVecMul_blockMatrixOfCoeff_snd A X,
    symmPart_matTranspose, skewPart_matTranspose]
  show -(matVecMul (symmPart A)⁻¹
      (matVecMul (-skewPart A) X.1 - -X.2)) =
    -(-(matVecMul (symmPart A)⁻¹ (matVecMul (skewPart A) X.1 - X.2)))
  rw [neg_matVecMul,
    show (-(matVecMul (skewPart A) X.1) - -X.2 : Vec d) =
      -(matVecMul (skewPart A) X.1 - X.2) by abel,
    matVecMul_neg]

/-- The doubled quadratic form is invariant under simultaneous transpose of
the coefficient matrix and flux flip of the doubled vector. -/
theorem blockQuadForm_transpose_fluxFlip (A : Mat d) (X : BlockVec d) :
    blockVecDot (X.1, -X.2)
        (blockMatVecMul (blockMatrixOfCoeff (matTranspose A)) (X.1, -X.2)) =
      blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) := by
  rw [blockQuadForm_blockMatrixOfCoeff (matTranspose A)
      ((X.1, -X.2) : BlockVec d),
    blockQuadForm_blockMatrixOfCoeff A X,
    symmPart_matTranspose, skewPart_matTranspose]
  show vecDot X.1 (matVecMul (symmPart A) X.1) +
      vecDot (matVecMul (-skewPart A) X.1 - -X.2)
        (matVecMul (symmPart A)⁻¹ (matVecMul (-skewPart A) X.1 - -X.2)) = _
  rw [neg_matVecMul,
    show (-(matVecMul (skewPart A) X.1) - -X.2 : Vec d) =
      -(matVecMul (skewPart A) X.1 - X.2) by abel,
    matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]

/-- **Exact pointwise second-difference expansion.**  For a skew perturbation
`g` of the coefficient matrix `A`, the doubled quadratic form expands exactly:
no remainder beyond the explicit quadratic term.  This is the pointwise core
of both the upper coarse-matrix expansion at the base field and (applied at
the shifted base) the lower expansion. -/
theorem blockQuadForm_add_skew (A : Mat d) {g : Mat d}
    (hg : symmPart g = 0) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockMatrixOfCoeff (A + g)) X) =
      blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X)
        - 2 * vecDot (matVecMul g X.1)
            ((blockMatVecMul (blockMatrixOfCoeff A) X).2)
        + vecDot (matVecMul g X.1)
            (matVecMul (symmPart A)⁻¹ (matVecMul g X.1)) := by
  have hsymm : symmPart (A + g) = symmPart A := by
    rw [symmPart_add, hg, add_zero]
  have hskew : skewPart (A + g) = skewPart A + g := by
    rw [skewPart_add, skewPart_eq_self_of_symmPart_eq_zero hg]
  have hsInv : ((symmPart A)⁻¹ : Mat d).IsSymm :=
    isSymm_nonsingInv (isSymm_symmPart A)
  rw [blockQuadForm_blockMatrixOfCoeff, blockQuadForm_blockMatrixOfCoeff,
    blockMatVecMul_blockMatrixOfCoeff_snd, hsymm, hskew]
  set s := symmPart A with hs
  set k := skewPart A with hk
  set u : Vec d := matVecMul k X.1 - X.2 with hu
  set w : Vec d := matVecMul g X.1 with hw
  have harg : matVecMul (k + g) X.1 - X.2 = u + w := by
    rw [add_matVecMul, hu, hw]
    abel
  rw [harg, matVecMul_add, vecDot_add_left, vecDot_add_right,
    vecDot_add_right, vecDot_neg_right]
  have hcomm : vecDot u (matVecMul s⁻¹ w) = vecDot w (matVecMul s⁻¹ u) :=
    vecDot_matVecMul_comm_of_isSymm hsInv u w
  rw [hcomm]
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path
