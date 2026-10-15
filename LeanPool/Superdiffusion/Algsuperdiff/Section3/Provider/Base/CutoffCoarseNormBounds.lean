/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CGBoundSpecialization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffFrobeniusMassMaximum
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.NormScaling

/-!
# CutoffCoarseNormBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Coarse-matrix norm bounds for the coefficient cutoff

This module turns the specialized cutoff Loewner chain into operator-norm
bounds on every triadic cube.  The upper coarse matrix is controlled by the
volume-normalized squared Frobenius mass of the stream, while the inverse
starred matrix is controlled deterministically by `nu⁻¹`.  Finite suprema give
the corresponding bounds over every fixed descendant depth.

The proof on an arbitrary cube is reduced to the centered cube of the same
scale.  `BadEvents.coarseBlockMatrix_cutoff_translateCutoffSample` supplies the
coarse-block covariance directly.  Translation invariance of normalized
volume averages identifies the centered Frobenius mass with the mass on the
original cube.  Thus no root-cube supremum replaces a translated local mass.

## Main results

* `coarseBMatrixNorm_coefficientCutoff_le` bounds the upper coarse-matrix norm
  on an arbitrary cube by `nu + nu⁻¹` times its cutoff Frobenius mass.
* `coarseSigmaStarInvMatrixNorm_coefficientCutoff_le` bounds the inverse
  starred coarse-matrix norm by `nu⁻¹`.
* `maxDescendantBMatrixNormAtScale_coefficientCutoff_le` and
  `maxDescendantSigmaStarInvMatrixNormAtScale_coefficientCutoff_le` give the
  corresponding fixed-depth descendant bounds.
-/

namespace Algsuperdiff.Section3.Provider.Base

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

private theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The cutoff Frobenius mass on an arbitrary cube is the centered mass of the
sample translated by the cube's base point. -/
private theorem cutoffFrobeniusMass_eq_translateCutoffSample
    (Q : TriadicCube d) (m : ℤ) (omega : CutoffSample d) :
    Stream.cutoffFrobeniusMass Q m omega =
      Stream.cutoffFrobeniusMass (originCube d Q.scale) m
        (translateCutoffSample (triadicCubeShift Q) omega) := by
  unfold Stream.cutoffFrobeniusMass
  change volumeAverage (openCubeSet Q)
      (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)) =
    volumeAverage (openCubeSet (originCube d Q.scale))
      (fun x => Ch02.matrixFrobeniusNormSq
        (cutoff m (translateCutoffSample (triadicCubeShift Q) omega) x))
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    Ch01.volumeAverage_translateSet_eq_comp_addRight]
  congr 1

private theorem matrixNorm_smul_one_eq_of_nonneg [NeZero d]
    {c : ℝ} (hc : 0 ≤ c) :
    Ch02.matrixNorm (c • (1 : Mat d)) = c := by
  simpa [Ch02.matrixNorm_eq_matrixOperatorNorm] using
    Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg (d := d) hc

private theorem coarseBMatrixNorm_originCube_coefficientCutoff_le
    (M : ABKModel d) (l m : ℤ) (omega : CutoffSample d) :
    Ch02.coarseBMatrixNorm (originCube d l)
        (coefficientCutoffTriadicCoeffFamily M m omega) ≤
      M.nu + M.nu⁻¹ * Stream.cutoffFrobeniusMass (originCube d l) m omega := by
  let : NeZero d := neZero_of_model M
  let mass := Stream.cutoffFrobeniusMass (originCube d l) m omega
  let c := M.nu * (1 + (M.nu ^ 2)⁻¹ * mass)
  have hmass : 0 ≤ mass := Stream.cutoffFrobeniusMass_nonneg _ _ _
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg M.nu_pos.le
      (add_nonneg zero_le_one
        (mul_nonneg (inv_nonneg.mpr (sq_nonneg M.nu)) hmass))
  have hscalar : (c • (1 : Mat d)).PosSemidef :=
    Matrix.PosSemidef.one.smul hc
  have hloewner : MatLoewnerLE
      (Ch02.bCoarse (Ch02.cubeDomain (originCube d l))
        (coefficientCutoffCoeffOn M m omega (originCube d l)))
      (c • (1 : Mat d)) := by
    simpa only [c, mass, Stream.cutoffFrobeniusMass] using
      matLoewnerLE_bCoarse_coefficientCutoff M l m omega
  have hnorm : Ch02.matrixNorm
      (Ch02.bCoarse (Ch02.cubeDomain (originCube d l))
        (coefficientCutoffCoeffOn M m omega (originCube d l))) ≤ c := by
    calc
      Ch02.matrixNorm
          (Ch02.bCoarse (Ch02.cubeDomain (originCube d l))
            (coefficientCutoffCoeffOn M m omega (originCube d l))) ≤
          Ch02.matrixNorm (c • (1 : Mat d)) :=
        Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
          (Ch02.bCoarse_posSemidef _ _) hscalar hloewner
      _ = c := matrixNorm_smul_one_eq_of_nonneg hc
  change Ch02.matrixNorm
      (Ch02.bCoarse (Ch02.cubeDomain (originCube d l))
        ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn
          (originCube d l))) ≤ _
  have hc_eq : c = M.nu + M.nu⁻¹ * mass := by
    dsimp [c]
    field_simp [M.nu_pos.ne']
  simpa only [coefficientCutoffTriadicCoeffFamily, mass, hc_eq] using hnorm

/-- On every triadic cube, the upper coarse-matrix norm of the cutoff is at
most `nu + nu⁻¹` times the local squared Frobenius mass. -/
theorem coarseBMatrixNorm_coefficientCutoff_le
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ) (omega : CutoffSample d) :
    Book.Ch02.coarseBMatrixNorm Q
      (coefficientCutoffTriadicCoeffFamily M m omega) ≤
      M.nu + M.nu⁻¹ * Stream.cutoffFrobeniusMass Q m omega := by
  let : NeZero d := neZero_of_model M
  rw [BadEvents.coarseBMatrixNorm_cutoff_translateCutoffSample M m
    (triadicCubeShift Q)
    (cubeSet_eq_translateSet_originCube_of_triadicCube Q) omega,
    cutoffFrobeniusMass_eq_translateCutoffSample Q m omega]
  exact coarseBMatrixNorm_originCube_coefficientCutoff_le M Q.scale m
    (translateCutoffSample (triadicCubeShift Q) omega)

private theorem coarseSigmaStarInvMatrixNorm_originCube_coefficientCutoff_le
    (M : ABKModel d) (l m : ℤ) (omega : CutoffSample d) :
    Ch02.coarseSigmaStarInvMatrixNorm (originCube d l)
        (coefficientCutoffTriadicCoeffFamily M m omega) ≤ M.nu⁻¹ := by
  let : NeZero d := neZero_of_model M
  let U := Ch02.cubeDomain (originCube d l)
  let a := coefficientCutoffCoeffOn M m omega (originCube d l)
  have hnuPos : (M.nu • (1 : Mat d)).PosDef :=
    Matrix.PosDef.one.smul M.nu_pos
  have hstarPos : (Ch02.sigmaStarCoarse U a).PosDef :=
    Ch02.sigmaStarCoarse_posDef U a
  have horder : MatLoewnerLE (M.nu • (1 : Mat d))
      (Ch02.sigmaStarCoarse U a) := by
    simpa only [U, a] using
      matLoewnerLE_nu_smul_one_sigmaStarCoarse_coefficientCutoff M m omega
        (originCube d l)
  have hinv := matLoewnerLE_inv_of_posDef hnuPos hstarPos horder
  have hleft : (Ch02.sigmaStarCoarse U a)⁻¹ = Ch02.sigmaStarInvCoarse U a := by
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U a)
  have hright : (M.nu • (1 : Mat d))⁻¹ = M.nu⁻¹ • (1 : Mat d) := by
    rw [nonsing_inv_smul M.nu M.nu_pos.ne' (by simp)]
    simp
  rw [hleft, hright] at hinv
  have hscalar : (M.nu⁻¹ • (1 : Mat d)).PosSemidef :=
    Matrix.PosSemidef.one.smul (inv_pos.mpr M.nu_pos).le
  have hnorm : Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) ≤ M.nu⁻¹ := by
    calc
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) ≤
          Ch02.matrixNorm (M.nu⁻¹ • (1 : Mat d)) :=
        Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
          (Ch02.sigmaStarInvCoarse_posDef U a).posSemidef hscalar hinv
      _ = M.nu⁻¹ := matrixNorm_smul_one_eq_of_nonneg
        (inv_pos.mpr M.nu_pos).le
  simpa only [Ch02.coarseSigmaStarInvMatrixNorm, U, a,
    coefficientCutoffTriadicCoeffFamily] using hnorm

/-- On every triadic cube, the inverse starred coarse-matrix norm of the
coefficient cutoff is at most `nu⁻¹`. -/
theorem coarseSigmaStarInvMatrixNorm_coefficientCutoff_le
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ) (omega : CutoffSample d) :
    Book.Ch02.coarseSigmaStarInvMatrixNorm Q
      (coefficientCutoffTriadicCoeffFamily M m omega) ≤ M.nu⁻¹ := by
  let : NeZero d := neZero_of_model M
  rw [BadEvents.coarseSigmaStarInvMatrixNorm_cutoff_translateCutoffSample M m
    (triadicCubeShift Q)
    (cubeSet_eq_translateSet_originCube_of_triadicCube Q) omega]
  exact coarseSigmaStarInvMatrixNorm_originCube_coefficientCutoff_le
    M Q.scale m (translateCutoffSample (triadicCubeShift Q) omega)

/-- At a fixed descendant depth, the maximal upper coarse-matrix norm is
controlled by the genuine maximum of the translated local Frobenius masses. -/
theorem maxDescendantBMatrixNormAtScale_coefficientCutoff_le
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ) (n : ℕ)
    (omega : CutoffSample d) :
    Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ))
      (coefficientCutoffTriadicCoeffFamily M m omega) ≤
      M.nu + M.nu⁻¹ * Stream.cutoffFrobeniusMassMaximum Q m n omega := by
  let : NeZero d := neZero_of_model M
  unfold Ch02.maxDescendantBMatrixNormAtScale
  refine Ch02.finsetSupReal_le _
    (descendantsAtScale_nonempty Q (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n))) ?_
  intro R hR
  have hRdepth : R ∈ descendantsAtDepth Q n := by
    have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
      sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
    simpa using hR
  calc
    Ch02.coarseBMatrixNorm R
        (coefficientCutoffTriadicCoeffFamily M m omega) ≤
        M.nu + M.nu⁻¹ * Stream.cutoffFrobeniusMass R m omega :=
      coarseBMatrixNorm_coefficientCutoff_le M R m omega
    _ ≤ M.nu + M.nu⁻¹ * Stream.cutoffFrobeniusMassMaximum Q m n omega :=
      add_le_add (le_refl M.nu)
        (mul_le_mul_of_nonneg_left
          (Stream.cutoffFrobeniusMass_le_cutoffFrobeniusMassMaximum
            Q m n hRdepth omega)
          (inv_pos.mpr M.nu_pos).le)

/-- At every fixed descendant depth, the maximal inverse starred coarse-matrix
norm of the coefficient cutoff is at most `nu⁻¹`. -/
theorem maxDescendantSigmaStarInvMatrixNormAtScale_coefficientCutoff_le
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ) (n : ℕ)
    (omega : CutoffSample d) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ))
      (coefficientCutoffTriadicCoeffFamily M m omega) ≤ M.nu⁻¹ := by
  let : NeZero d := neZero_of_model M
  unfold Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  refine Ch02.finsetSupReal_le _
    (descendantsAtScale_nonempty Q (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n))) ?_
  intro R _hR
  exact coarseSigmaStarInvMatrixNorm_coefficientCutoff_le M R m omega

end

end Algsuperdiff.Section3.Provider.Base
