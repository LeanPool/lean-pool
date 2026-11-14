/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.KappaZero

/-!
# Diagonal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Block diagonality of the annealed cutoff block matrix

ABK26, `e.homs.defs.U.diag`.  Once the annealed coupling matrix vanishes
(`e.annealed.khom.zero`), the display records that `bhom_m(U) = shom_m(U)` and
that the annealed doubled matrix is block diagonal, `bfAhom_m(U) = ((shom_m(U),
0), (0, shom_{m,*}^{-1}(U)))`.

In CoarseGraining's naming the finite-volume annealed blocks of `bfAhom_m(U) =
E[bfA_m(U)]` are `Ch04.annealedB` (upper left `bhom_m(U)`),
`Ch04.annealedSigmaStarInv` (lower right `shom_{m,*}^{-1}(U)`) and
`Ch04.annealedSigma` (`shom_m(U)`), with the two mixed blocks `-(khom_m^t
shom_{m,*}^{-1})(U)` and `-(shom_{m,*}^{-1} khom_m)(U)` sitting in `upperRight`
and `lowerLeft`.

## Main results

* `coefficientCutoffLaw_annealedSigma_eq_annealedB`
* `coefficientCutoffLaw_annealedBlockMatrix_eq_blockDiag`
* `coefficientCutoffLaw_annealedBlockMatrixAtScale_eq_blockDiag`
-/

namespace Algsuperdiff.Section3.Provider.Annealed

open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Two doubled block matrices agree as soon as their four blocks agree. -/
private theorem blockMat_eq_of_blocks {A B : BlockMat d}
    (hUL : A.upperLeft = B.upperLeft) (hUR : A.upperRight = B.upperRight)
    (hLL : A.lowerLeft = B.lowerLeft) (hLR : A.lowerRight = B.lowerRight) :
    A = B := by
  cases A
  cases B
  simp only [BlockMat.mk.injEq]
  exact ⟨hUL, hUR, hLL, hLR⟩

/-- **ABK26, `bhom_m(U) = shom_m(U)`.**  The annealed conductivity of the
genuine cutoff equals its annealed upper-left block. -/
theorem coefficientCutoffLaw_annealedSigma_eq_annealedB
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    Ch04.annealedSigma (Cutoff.coefficientCutoffLaw M m) (cubeSet Q) =
      Ch04.annealedB (Cutoff.coefficientCutoffLaw M m) (cubeSet Q) := by
  rw [Ch04.annealedSigma, coefficientCutoffLaw_annealedKappa_eq_zero M m Q,
    mul_zero, sub_zero]

/-- **ABK26, `e.homs.defs.U.diag`.**  The annealed doubled block matrix of the
genuine coefficient cutoff is block diagonal on every triadic cube, with
diagonal blocks `shom_m(U)` and `shom_{m,*}^{-1}(U)`. -/
theorem coefficientCutoffLaw_annealedBlockMatrix_eq_blockDiag
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q) =
      Ch02.blockDiag
        (Ch04.annealedSigma (Cutoff.coefficientCutoffLaw M m) (cubeSet Q))
        (Ch04.annealedSigmaStarInv (Cutoff.coefficientCutoffLaw M m) (cubeSet Q)) := by
  refine blockMat_eq_of_blocks ?_ ?_ ?_ rfl
  · exact (coefficientCutoffLaw_annealedSigma_eq_annealedB M m Q).symm
  · exact coefficientCutoffLaw_annealedBlockMatrix_upperRight_eq_zero M m Q
  · exact coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero M m Q

/-- Origin-cube form of
`coefficientCutoffLaw_annealedBlockMatrix_eq_blockDiag`. -/
theorem coefficientCutoffLaw_annealedBlockMatrixAtScale_eq_blockDiag
    (M : ABKModel d) (m : ℤ) (n : ℤ) :
    Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n =
      Ch02.blockDiag
        (Ch04.annealedSigmaAtScale (Cutoff.coefficientCutoffLaw M m) n)
        (Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M m) n) :=
  coefficientCutoffLaw_annealedBlockMatrix_eq_blockDiag M m (originCube d n)

end

end Algsuperdiff.Section3.Provider.Annealed
