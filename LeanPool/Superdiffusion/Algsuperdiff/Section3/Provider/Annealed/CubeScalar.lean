/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Diagonal
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.Scalarization

/-!
# CubeScalar

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Scalarity of the annealed diagonal blocks on cubes

ABK26: the hypercube symmetry assumption also implies, in the case that `U =
cu` is a cube, that each of the diagonal blocks of `bfAhom_m(cu)` is a scalar
matrix.

The mechanism is CoarseGraining's Chapter 4 scalarization route
(`Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint`),
which needs only a law carrier, signed-permutation isotropy in law, and adjoint
invariance in law.  All three are already proved for the genuine cutoff law, so
no structural-law (in particular no unit-range) hypothesis is used here.

## Main results

* `coefficientCutoffLaw_isScalarMatrix_annealedBAtScale`
* `coefficientCutoffLaw_isScalarMatrix_annealedSigmaStarInvAtScale`
* `coefficientCutoffLaw_isScalarMatrix_annealedSigmaAtScale`
* `coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one`
-/

namespace Algsuperdiff.Section3.Provider.Annealed

open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The Chapter 4 primitive scalarization data of the genuine cutoff law at a
fixed origin-cube scale, built from the law carrier, isotropy and adjoint
invariance only. -/
private theorem cutoffPrimitiveScalarizationData
    (M : ABKModel d) (m : ℤ) (n : ℤ) :
    Ch04.Internal.AnnealedPrimitiveScalarizationData
      (Cutoff.coefficientCutoffLaw M m) n :=
  Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    (Cutoff.coefficientCutoffLaw_lawCarrier M m)
    (Cutoff.coefficientCutoffLaw_isotropic M m)
    (Cutoff.coefficientCutoffLaw_adjoint_invariant M m) n

/-- **ABK26.**  The annealed upper-left block of the genuine cutoff on an origin
cube is a scalar matrix. -/
theorem coefficientCutoffLaw_isScalarMatrix_annealedBAtScale
    (M : ABKModel d) (m : ℤ) (n : ℤ) :
    IsScalarMatrix (Ch04.annealedBAtScale (Cutoff.coefficientCutoffLaw M m) n) :=
  Ch04.Internal.annealedBAtScale_isScalarMatrix_of_invariant
    (Cutoff.coefficientCutoffLaw M m) n
    (cutoffPrimitiveScalarizationData M m n).bFlip
    (cutoffPrimitiveScalarizationData M m n).bSwap

/-- **ABK26.**  The annealed inverse-star block of the genuine cutoff on an
origin cube is a scalar matrix. -/
theorem coefficientCutoffLaw_isScalarMatrix_annealedSigmaStarInvAtScale
    (M : ABKModel d) (m : ℤ) (n : ℤ) :
    IsScalarMatrix
      (Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M m) n) :=
  Ch04.Internal.annealedSigmaStarInvAtScale_isScalarMatrix_of_invariant
    (Cutoff.coefficientCutoffLaw M m) n
    (cutoffPrimitiveScalarizationData M m n).sigmaStarInvFlip
    (cutoffPrimitiveScalarizationData M m n).sigmaStarInvSwap

/-- The annealed conductivity of the genuine cutoff on an origin cube is a
scalar matrix. -/
theorem coefficientCutoffLaw_isScalarMatrix_annealedSigmaAtScale
    (M : ABKModel d) (m : ℤ) (n : ℤ) :
    IsScalarMatrix (Ch04.annealedSigmaAtScale (Cutoff.coefficientCutoffLaw M m) n) :=
  Ch04.Internal.annealedSigmaAtScale_isScalarMatrix_of_bInvariant_of_sigmaStarInvKappaMean_eq_zero
    (Cutoff.coefficientCutoffLaw M m) n
    (cutoffPrimitiveScalarizationData M m n).bFlip
    (cutoffPrimitiveScalarizationData M m n).bSwap
    (cutoffPrimitiveScalarizationData M m n).sigmaStarInvKappaMean_eq_zero

/-- **ABK26 combined.**  On an origin cube the annealed cutoff block
matrix is block diagonal with scalar diagonal blocks. -/
theorem coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one
    (M : ABKModel d) (m : ℤ) (n : ℤ) :
    ∃ s t : ℝ,
      Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n =
        Ch02.blockDiag (s • (1 : Mat d)) (t • (1 : Mat d)) := by
  obtain ⟨s, hs⟩ := coefficientCutoffLaw_isScalarMatrix_annealedSigmaAtScale M m n
  obtain ⟨t, ht⟩ :=
    coefficientCutoffLaw_isScalarMatrix_annealedSigmaStarInvAtScale M m n
  refine ⟨s, t, ?_⟩
  rw [coefficientCutoffLaw_annealedBlockMatrixAtScale_eq_blockDiag M m n, hs, ht]

end

end Algsuperdiff.Section3.Provider.Annealed
