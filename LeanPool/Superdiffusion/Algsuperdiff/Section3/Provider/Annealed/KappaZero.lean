/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LawCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.AnnealedDefinitions
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.CoarseObservables
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.AdjointSymmetry.BasicAdjoint

/-!
# KappaZero

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Vanishing of the annealed coupling matrix of the cutoff law

ABK26, `e.annealed.khom.zero`: by the adjoint redundancy of
the coarse-grained block matrix and the hypercube-symmetry assumption that
`a_m` has the same law as `a_m^t`, the annealed coupling matrix vanishes on
every cube,
`khom_m(U) = 0`.

The two mixed blocks of the deterministic coarse block matrix flip sign under
`a -> a^t` (CoarseGraining's
`coarseBlockMatrix_lowerLeft_adjointCoeffField_of_exists` and
`coarseBlockMatrix_upperRight_adjointCoeffField_of_exists`), and the actual
cutoff law is adjoint invariant
(`Algsuperdiff.Section3.Cutoff.coefficientCutoffLaw_adjoint_invariant`), so
each mixed annealed entry equals its own negative.

## Main results

* `coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero`
* `coefficientCutoffLaw_annealedBlockMatrix_upperRight_eq_zero`
* `coefficientCutoffLaw_annealedSigmaStarInvKappaMean_eq_zero`
* `coefficientCutoffLaw_annealedKappa_eq_zero`
-/

namespace Algsuperdiff.Section3.Provider.Annealed

open MeasureTheory
open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The carrier adjoint is the entrywise adjoint of the honest sample. -/
private theorem adjointReg_toFun (a : RegCoeffField d) :
    (adjointReg a).toFun = adjointCoeffField a.toFun := rfl

omit [NeZero d] in
/-- An observable that is odd under the adjoint has vanishing expectation
under an adjoint-invariant law. -/
private theorem integral_eq_zero_of_adjointReg_neg {P : Ch04.RestrictionCoeffLaw d}
    (hAdj : Ch04.RestrictionAdjointInvariantLaw P) (G : RegCoeffField d → ℝ)
    (hmeas : AEStronglyMeasurable G P)
    (hcov : ∀ᵐ a ∂P, G (adjointReg a) = -G a) :
    ∫ a, G a ∂P = 0 := by
  have hcomp : ∫ a, G (adjointReg a) ∂P = ∫ a, G a ∂P :=
    hAdj.integral_comp_adjointReg G hmeas
  have hneg : ∫ a, G (adjointReg a) ∂P = -∫ a, G a ∂P := by
    rw [integral_congr_ae hcov]
    exact integral_neg G
  linarith [hcomp, hneg]

/-- The lower-left coarse block flips sign under the adjoint, almost surely
under any Chapter 4 restriction-law carrier. -/
private theorem coarseBlockMatrix_lowerLeft_adjointReg_ae
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (Q : TriadicCube d) :
    ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet Q) (adjointReg a).toFun).lowerLeft =
        -((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft) := by
  filter_upwards [hP.ae_exists_coarseBlockMatrix_openCubeSet Q] with a ha
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q (adjointReg a).toFun,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a.toFun, adjointReg_toFun]
  exact coarseBlockMatrix_lowerLeft_adjointCoeffField_of_exists
    (U := openCubeSet Q) (a := a.toFun) ha

/-- The upper-right coarse block flips sign under the adjoint, almost surely
under any Chapter 4 restriction-law carrier. -/
private theorem coarseBlockMatrix_upperRight_adjointReg_ae
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (Q : TriadicCube d) :
    ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet Q) (adjointReg a).toFun).upperRight =
        -((coarseBlockMatrix (cubeSet Q) a.toFun).upperRight) := by
  filter_upwards [hP.ae_exists_coarseBlockMatrix_openCubeSet Q] with a ha
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q (adjointReg a).toFun,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a.toFun, adjointReg_toFun]
  exact coarseBlockMatrix_upperRight_adjointCoeffField_of_exists
    (U := openCubeSet Q) (a := a.toFun) ha

/-- The lower-left annealed block of the genuine cutoff law vanishes on every
triadic cube. -/
theorem coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q)).lowerLeft =
      0 := by
  have hP : Ch04.RestrictionLawCarrier (Cutoff.coefficientCutoffLaw M m) :=
    Cutoff.coefficientCutoffLaw_lawCarrier M m
  ext i j
  rw [Ch04.annealedBlockMatrix_lowerLeft_apply, Matrix.zero_apply]
  refine integral_eq_zero_of_adjointReg_neg
    (Cutoff.coefficientCutoffLaw_adjoint_invariant M m)
    (fun a => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft i j)
    (hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j).aestronglyMeasurable ?_
  filter_upwards [coarseBlockMatrix_lowerLeft_adjointReg_ae hP Q] with a ha
  simpa using congrArg (fun A : Mat d => A i j) ha

/-- The upper-right annealed block of the genuine cutoff law vanishes on every
triadic cube. -/
theorem coefficientCutoffLaw_annealedBlockMatrix_upperRight_eq_zero
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q)).upperRight =
      0 := by
  have hP : Ch04.RestrictionLawCarrier (Cutoff.coefficientCutoffLaw M m) :=
    Cutoff.coefficientCutoffLaw_lawCarrier M m
  ext i j
  rw [Ch04.annealedBlockMatrix_upperRight_apply, Matrix.zero_apply]
  refine integral_eq_zero_of_adjointReg_neg
    (Cutoff.coefficientCutoffLaw_adjoint_invariant M m)
    (fun a => (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight i j)
    (hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j).aestronglyMeasurable ?_
  filter_upwards [coarseBlockMatrix_upperRight_adjointReg_ae hP Q] with a ha
  simpa using congrArg (fun A : Mat d => A i j) ha

/-- The annealed mixed observable `E[sigma_*^{-1}(U; a) kappa(U; a)]` of the
genuine cutoff law vanishes on every triadic cube. -/
theorem coefficientCutoffLaw_annealedSigmaStarInvKappaMean_eq_zero
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    Ch04.annealedSigmaStarInvKappaMean (Cutoff.coefficientCutoffLaw M m) (cubeSet Q) =
      0 := by
  rw [Ch04.annealedSigmaStarInvKappaMean,
    coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero M m Q, neg_zero]

/-- **ABK26, `e.annealed.khom.zero`.**  The annealed coupling matrix of the
genuine coefficient cutoff vanishes on every triadic cube. -/
theorem coefficientCutoffLaw_annealedKappa_eq_zero
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    Ch04.annealedKappa (Cutoff.coefficientCutoffLaw M m) (cubeSet Q) = 0 := by
  rw [Ch04.annealedKappa,
    coefficientCutoffLaw_annealedSigmaStarInvKappaMean_eq_zero M m Q, mul_zero]

end

end Algsuperdiff.Section3.Provider.Annealed
