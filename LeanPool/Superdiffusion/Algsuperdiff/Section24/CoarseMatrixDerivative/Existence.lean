/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.Polarization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.ResponsePairing

/-!
# Existence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Existence and uniqueness of the coarse-matrix derivative

The canonical response gradients construct the matrix by polarization.  A.e.
gradient uniqueness then upgrades the construction to the source statement for
arbitrary maximizing representatives.
-/

namespace Algsuperdiff.Section24.CoarseMatrixDerivative.Internal

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

theorem existsUnique_coarseMatrixDerivative
    (U : Domain d) (a : CoeffOn U) (h : LInfMatrixFieldOn U) :
    ∃! D : BlockMat d,
      IsSymmetricBlockMat D ∧
      ∀ p q : Vec d, ∀ vAdj : Solution U a.transpose, ∀ v : Solution U a,
        IsResponseMaximizer U a.transpose p q vAdj →
        IsResponseMaximizer U a p (-q) v →
        blockVecDot (p, q) (blockMatVecMul D (p, q)) =
          average U (fun x =>
            vecDot (vAdj.toH1.grad x) (matVecMul (h.1 x) (v.toH1.grad x))) := by
  let D : BlockMat d := blockMatOfQuadForm (quadraticForm U a h)
  refine ⟨D, ?_, ?_⟩
  · constructor
    · exact isSymmetricBlockMat_blockMatOfQuadForm _
    · intro p q vAdj v hvAdj hv
      calc
        blockVecDot (p, q) (blockMatVecMul D (p, q)) =
            average U (fun x =>
              vecDot
                ((canonicalMaximizer
                  (responseExistenceTheory U a.transpose) p q).toSolution.toH1.grad x)
                (matVecMul (h.1 x)
                  ((canonicalMaximizer
                    (responseExistenceTheory U a) p (-q)).toSolution.toH1.grad x))) := by
              unfold D quadraticForm
              simpa [pairing, adjointResponseGradient, primalResponseGradient] using!
                (blockVecDot_blockMatVecMul_blockMatOfQuadForm_of_bilin (pairing U a h)
                  (pairing_add_left U a h)
                  (pairing_smul_left U a h)
                  (pairing_add_right U a h)
                  (pairing_smul_right U a h) (p, q))
        _ = average U (fun x =>
              vecDot (vAdj.toH1.grad x) (matVecMul (h.1 x) (v.toH1.grad x))) :=
          average_eq_of_isResponseMaximizers U a h p q vAdj v hvAdj hv
  · intro A hA
    rcases hA with ⟨hAsymm, hAquad⟩
    have hAquadP : ∀ P : BlockVec d,
        blockVecDot P (blockMatVecMul A P) = quadraticForm U a h P := by
      rintro ⟨p, q⟩
      let vAdj :=
        (canonicalMaximizer (responseExistenceTheory U a.transpose) p q).toSolution
      let v := (canonicalMaximizer (responseExistenceTheory U a) p (-q)).toSolution
      have hcanonical := hAquad p q vAdj v
        (canonicalMaximizer_isMaximizer (responseExistenceTheory U a.transpose) p q)
        (canonicalMaximizer_isMaximizer (responseExistenceTheory U a) p (-q))
      simpa [vAdj, v, quadraticForm, pairing, adjointResponseGradient,
        primalResponseGradient] using! hcanonical
    have hDquad : ∀ P : BlockVec d,
        blockVecDot P (blockMatVecMul D P) = quadraticForm U a h P := by
      intro P
      unfold D quadraticForm
      exact blockVecDot_blockMatVecMul_blockMatOfQuadForm_of_bilin (pairing U a h)
        (pairing_add_left U a h)
        (pairing_smul_left U a h)
        (pairing_add_right U a h)
        (pairing_smul_right U a h) P
    have hDsymm : IsSymmetricBlockMat D := by
      unfold D
      exact isSymmetricBlockMat_blockMatOfQuadForm _
    have hentry : ∀ α β : BlockCoord d,
        blockMatEntry A α β = blockMatEntry D α β := by
      intro α β
      have hdiagα : blockMatEntry A α α = blockMatEntry D α α := by
        calc
          blockMatEntry A α α =
              blockVecDot (blockBasis α) (blockMatVecMul A (blockBasis α)) :=
            (blockBasis_pairing A α α).symm
          _ = quadraticForm U a h (blockBasis α) := hAquadP _
          _ = blockVecDot (blockBasis α) (blockMatVecMul D (blockBasis α)) :=
            (hDquad _).symm
          _ = blockMatEntry D α α := blockBasis_pairing D α α
      have hdiagβ : blockMatEntry A β β = blockMatEntry D β β := by
        calc
          blockMatEntry A β β =
              blockVecDot (blockBasis β) (blockMatVecMul A (blockBasis β)) :=
            (blockBasis_pairing A β β).symm
          _ = quadraticForm U a h (blockBasis β) := hAquadP _
          _ = blockVecDot (blockBasis β) (blockMatVecMul D (blockBasis β)) :=
            (hDquad _).symm
          _ = blockMatEntry D β β := blockBasis_pairing D β β
      have hsum :
          blockMatEntry A α α + blockMatEntry A α β +
              blockMatEntry A β α + blockMatEntry A β β =
            blockMatEntry D α α + blockMatEntry D α β +
              blockMatEntry D β α + blockMatEntry D β β := by
        calc
          blockMatEntry A α α + blockMatEntry A α β +
                blockMatEntry A β α + blockMatEntry A β β =
              blockVecDot (blockBasis α + blockBasis β)
                (blockMatVecMul A (blockBasis α + blockBasis β)) :=
            (blockBasis_sum_pairing A α β).symm
          _ = quadraticForm U a h (blockBasis α + blockBasis β) := hAquadP _
          _ = blockVecDot (blockBasis α + blockBasis β)
                (blockMatVecMul D (blockBasis α + blockBasis β)) := (hDquad _).symm
          _ = blockMatEntry D α α + blockMatEntry D α β +
                blockMatEntry D β α + blockMatEntry D β β :=
            blockBasis_sum_pairing D α β
      rw [← hAsymm α β, ← hDsymm α β] at hsum
      linarith
    apply blockMat_ext
    · funext i j
      simpa [blockMatEntry] using hentry (Sum.inl i) (Sum.inl j)
    · funext i j
      simpa [blockMatEntry] using hentry (Sum.inl i) (Sum.inr j)
    · funext i j
      simpa [blockMatEntry] using hentry (Sum.inr i) (Sum.inl j)
    · funext i j
      simpa [blockMatEntry] using hentry (Sum.inr i) (Sum.inr j)

end

end Algsuperdiff.Section24.CoarseMatrixDerivative.Internal
