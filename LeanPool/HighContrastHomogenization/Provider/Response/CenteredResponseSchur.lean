/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAdjointAnnealed

/-!
# High-contrast homogenization: Provider.Response.CenteredResponseSchur

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur-coordinate annealed identities

When the annealed coarse block is written in its positive Schur form, the
annealed primal and adjoint energies and optimizer means have the explicit
coordinate formulas used by the centered-response calculation.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The project and matrix-library notations for matrix-vector multiplication
agree. -/
theorem matVecMul_eq_matrix_mulVec (A : Mat d) (x : Vec d) :
    matVecMul A x = A *ᵥ x := rfl

/-- Equality of flattened annealed blocks can be read as equality with the
structural block induced by the Schur matrix. -/
theorem annealedBlock_eq_schur
    {P : Measure (CoeffSpace d)} (U : Domain d) {S SStar K : Mat d}
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) :
    annealedBlock P (U : Set (Vec d)) =
      ofFullBlockMat (schurBlock S SStar K) := by
  apply toFullBlockMat_injective
  simpa using hE

/-- The structural form of a Schur block. -/
theorem ofFullBlockMat_schurBlock (S SStar K : Mat d) :
    ofFullBlockMat (schurBlock S SStar K) =
      { upperLeft := S + Kᴴ * SStar⁻¹ * K
        upperRight := -(Kᴴ * SStar⁻¹)
        lowerLeft := -(SStar⁻¹ * K)
        lowerRight := SStar⁻¹ } := by
  rw [schurBlock_eq]
  rfl

/-- The primal annealed response energy in Schur coordinates. -/
theorem annealed_responseJ_schur {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d}
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p q : Vec d) :
    (∫ a, responseJ U (a.coeffOn U) p q ∂P) =
      (1 / 2 : ℝ) * (p ⬝ᵥ S *ᵥ p) +
        (1 / 2 : ℝ) * ((q + K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q + K *ᵥ p)) - vecDot p q := by
  rw [annealed_responseJ_eq U hint p q,
    blockVecDot_blockMatVecMul_eq_dotProduct, hE]
  have hX : toFullBlockVec ((-p, q) : BlockVec d) = Sum.elim (-p) q := by
    funext α
    cases α <;> rfl
  rw [hX]
  rw [quadratic_schurBlock]
  simp only [Matrix.mulVec_neg, sub_neg_eq_add, dotProduct_neg, neg_dotProduct,
    neg_neg]
  ring_nf

/-- The adjoint annealed response energy in the original Schur coordinates. -/
theorem annealed_adjoint_responseJ_schur {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d}
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p q : Vec d) :
    (∫ a, responseJ U (a.transpose.coeffOn U) p q ∂P) =
      (1 / 2 : ℝ) * (p ⬝ᵥ S *ᵥ p) +
        (1 / 2 : ℝ) * ((q - K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q - K *ᵥ p)) - vecDot p q := by
  rw [annealed_adjoint_responseJ_eq U hint p q,
    blockQuadratic_adjointSign_congr, adjointSign_mulVec,
    blockVecDot_blockMatVecMul_eq_dotProduct, hE]
  have hX : toFullBlockVec ((-p, -q) : BlockVec d) = Sum.elim (-p) (-q) := by
    funext α
    cases α <;> rfl
  rw [hX]
  rw [quadratic_schurBlock]
  simp only [Matrix.mulVec_neg, neg_sub_neg, dotProduct_neg, neg_dotProduct,
    neg_neg]
  have hneg : K *ᵥ p - q = -(q - K *ᵥ p) := by abel
  rw [hneg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  ring_nf

/-- The two rows of the Schur block applied to the primal signed load. -/
theorem blockR_schur_mulVec_primal (S SStar K : Mat d) (p q : Vec d) :
    blockMatVecMul (blockR d)
        (blockMatVecMul (ofFullBlockMat (schurBlock S SStar K))
          ((-p, q) : BlockVec d)) + ((-p, q) : BlockVec d) =
      ((-p + SStar⁻¹ *ᵥ (q + K *ᵥ p),
        (1 - Kᴴ * SStar⁻¹) *ᵥ q -
          (S + Kᴴ * SStar⁻¹ * K) *ᵥ p) : BlockVec d) := by
  rw [ofFullBlockMat_schurBlock, blockMatVecMul_blockR]
  apply Prod.ext
  · change
      (matVecMul (-(SStar⁻¹ * K)) (-p) + matVecMul SStar⁻¹ q) + -p =
        -p + SStar⁻¹ *ᵥ (q + K *ᵥ p)
    simp_rw [matVecMul_eq_matrix_mulVec]
    rw [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.mulVec_add,
      Matrix.mulVec_mulVec]
    abel
  · change
      (matVecMul (S + Kᴴ * SStar⁻¹ * K) (-p) +
          matVecMul (-(Kᴴ * SStar⁻¹)) q) + q =
        (1 - Kᴴ * SStar⁻¹) *ᵥ q -
          (S + Kᴴ * SStar⁻¹ * K) *ᵥ p
    simp_rw [matVecMul_eq_matrix_mulVec]
    rw [Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    abel

/-- The two rows of the signed Schur block applied to the adjoint load. -/
theorem blockR_adjoint_schur_mulVec (S SStar K : Mat d) (p q : Vec d) :
    blockMatVecMul (blockR d)
        (blockMatVecMul
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul (ofFullBlockMat (schurBlock S SStar K))
              (blockDiag 1 (-1)))) ((-p, q) : BlockVec d)) +
        ((-p, q) : BlockVec d) =
      ((-p + SStar⁻¹ *ᵥ (q - K *ᵥ p),
        (1 + Kᴴ * SStar⁻¹) *ᵥ q -
          (S + Kᴴ * SStar⁻¹ * K) *ᵥ p) : BlockVec d) := by
  rw [blockMatVecMul_adjointSign_congr, adjointSign_mulVec,
    adjointSign_mulVec, ofFullBlockMat_schurBlock, blockMatVecMul_blockR]
  apply Prod.ext
  · change
      -(matVecMul (-(SStar⁻¹ * K)) (-p) + matVecMul SStar⁻¹ (-q)) + -p =
        -p + SStar⁻¹ *ᵥ (q - K *ᵥ p)
    simp_rw [matVecMul_eq_matrix_mulVec]
    simp only [Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, neg_neg]
    abel
  · change
      (matVecMul (S + Kᴴ * SStar⁻¹ * K) (-p) +
          matVecMul (-(Kᴴ * SStar⁻¹)) (-q)) + q =
        (1 + Kᴴ * SStar⁻¹) *ᵥ q -
          (S + Kᴴ * SStar⁻¹ * K) *ᵥ p
    simp_rw [matVecMul_eq_matrix_mulVec]
    simp only [Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, neg_neg]
    abel

/-- The two separately annealed primal optimizer means in Schur coordinates. -/
theorem annealed_optimizer_means_schur {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d}
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p q : Vec d) :
    ((annealedOptimizerGradient P U p q,
        annealedOptimizerFlux P U p q) : BlockVec d) =
      ((-p + SStar⁻¹ *ᵥ (q + K *ᵥ p),
        (1 - Kᴴ * SStar⁻¹) *ᵥ q -
          (S + Kᴴ * SStar⁻¹ * K) *ᵥ p) : BlockVec d) := by
  rw [annealed_optimizer_average_eq U hint p q,
    annealedBlock_eq_schur U hE]
  exact blockR_schur_mulVec_primal S SStar K p q

/-- The two separately annealed adjoint optimizer means in Schur coordinates. -/
theorem annealed_adjoint_optimizer_means_schur
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d}
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p q : Vec d) :
    ((annealedAdjointOptimizerGradient P U p q,
        annealedAdjointOptimizerFlux P U p q) : BlockVec d) =
      ((-p + SStar⁻¹ *ᵥ (q - K *ᵥ p),
        (1 + Kᴴ * SStar⁻¹) *ᵥ q -
          (S + Kᴴ * SStar⁻¹ * K) *ᵥ p) : BlockVec d) := by
  rw [annealed_adjoint_optimizer_average_eq U hint p q,
    annealedBlock_eq_schur U hE]
  exact blockR_adjoint_schur_mulVec S SStar K p q

end

end HCPolySupport.HighContrast.Response
