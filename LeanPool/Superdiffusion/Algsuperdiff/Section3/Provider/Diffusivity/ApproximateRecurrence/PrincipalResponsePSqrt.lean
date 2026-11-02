/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block

/-!
# PrincipalResponsePSqrt

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the annealed limit block matrix and its two square roots

Source displays in ABK26:

* `e.homs.defs` (label; display) defines the deterministic infinite-volume
  annealed doubled matrix `bfAhom_m = ((shom_m, 0), (0, shom_m^{-1}))`, where
  rules that `shom_m` is a *scalar* matrix, "a positive scalar matrix, or a
  positive real number, whichever is convenient".
* `e.homs.defs.U.diag` (label) is the finite-volume block diagonality that the
  limit inherits; it is already realized in this repository by
  `Provider.Annealed.coefficientCutoffLaw_annealedBlockMatrixAtScale_eq_blockDiag`.
* `e.recurrence.P.def` (label) and `e.Pz.def` (label) apply the *inverse square
  root* `bfAhom_{m-h}^{-1/2}` to a doubled load applies the square root
  `bfAhom_{m-h}^{1/2}`.  This module builds those two matrices and pins them
  down; the loads themselves are built downstream.

## Why no matrix functional calculus is needed

Because `shom_m` is a positive real, `bfAhom_m` is the *scalar* block diagonal
`blockDiag (sigma . 1) (sigma^{-1} . 1)`, so its square root and inverse square
root are the elementary `blockDiag (sqrt sigma . 1) ((sqrt sigma)^{-1} . 1)`
and `blockDiag ((sqrt sigma)^{-1} . 1) (sqrt sigma . 1)`.  Nothing here uses a
spectral decomposition: the two matrices are pinned down by their action on a
doubled load, which at a scalar block diagonal is elementary.

The carrier of the positive real is the repository's own running diffusivity
type `Algsuperdiff.Section3.Observable.PositiveScalar`, on which positivity is
part of the type; `annealedLimitBlock_sigmaBar_characterization` records that
`annealedLimitBlock (sigmaBar M m)` really is the infinite-volume annealed limit
of the genuine coefficient cutoff, and that no other positive scalar has that
limit.

## Main results

* `annealedLimitBlock`, `annealedLimitBlockSqrt`, `annealedLimitBlockInvSqrt`
* `annealedLimitBlock_sigmaBar_characterization`
* `blockMatVecMul_annealedLimitBlockInvSqrt`,
  `blockMatVecMul_annealedLimitBlockSqrt`: the two square roots act on a doubled
  load by the scalar loads `inverseSqrtLoad` and `sqrtLoad`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open Filter HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The three matrices -/

/-- **`e.homs.defs`.**  The deterministic infinite-volume annealed doubled matrix
`bfAhom_m = ((shom_m, 0), (0, shom_m^{-1}))` at a positive scalar `shom_m`. -/
def annealedLimitBlock (sigma : PositiveScalar) : BlockMat d :=
  Ch02.blockDiag ((sigma : ℝ) • (1 : Mat d)) ((sigma : ℝ)⁻¹ • (1 : Mat d))

/-- The square root `bfAhom_m^{1/2}` used. -/
def annealedLimitBlockSqrt (sigma : PositiveScalar) : BlockMat d :=
  Ch02.blockDiag (Real.sqrt (sigma : ℝ) • (1 : Mat d))
    ((Real.sqrt (sigma : ℝ))⁻¹ • (1 : Mat d))

/-- The inverse square root `bfAhom_m^{-1/2}` used at `e.recurrence.P.def` and
`e.Pz.def`. -/
def annealedLimitBlockInvSqrt (sigma : PositiveScalar) : BlockMat d :=
  Ch02.blockDiag ((Real.sqrt (sigma : ℝ))⁻¹ • (1 : Mat d))
    (Real.sqrt (sigma : ℝ) • (1 : Mat d))

/-! ## The annealed limit really is the infinite-volume annealed limit -/

/-- **`e.homs.defs` at the genuine cutoff.**  The doubled annealed matrices of the
genuine coefficient cutoff converge to `annealedLimitBlock (sigmaBar M m)`, and
no other positive scalar produces that limit.  This is
`Annealed.sigmaBar_characterization` read through `annealedLimitBlock`. -/
theorem annealedLimitBlock_sigmaBar_characterization (M : ABKModel d) (m : ℤ) :
    Tendsto
        (fun n : ℕ =>
          toFullBlockMat
            (Ch04.annealedBlockMatrixAtScale
              (Cutoff.coefficientCutoffLaw M m) (n : ℤ)))
        atTop
        (nhds (toFullBlockMat
          (annealedLimitBlock (d := d) (Annealed.sigmaBar M m)))) ∧
      ∀ other : PositiveScalar,
        Tendsto
          (fun n : ℕ =>
            toFullBlockMat
              (Ch04.annealedBlockMatrixAtScale
                (Cutoff.coefficientCutoffLaw M m) (n : ℤ)))
          atTop
          (nhds (toFullBlockMat (annealedLimitBlock (d := d) other))) →
          other = Annealed.sigmaBar M m := by
  obtain ⟨-, hlim, huniq⟩ := Annealed.sigmaBar_characterization M m
  refine ⟨hlim, ?_⟩
  intro other hother
  exact Subtype.ext (huniq (other : ℝ) other.2 hother)

/-! ## Elementary block algebra of the scalar block diagonals -/

/-- A scalar multiple of the identity acts on a vector by that scalar. -/
theorem matVecMul_smul_one (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  rw [smul_matVecMul]
  congr 1
  funext i
  simp [matVecMul, Matrix.one_apply]

private theorem zero_matVecMul (x : Vec d) :
    matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

/-! ## The defining property: the square is the inverse -/

/-- Doubled matrix-vector multiplication is compatible with doubled matrix
multiplication. -/
theorem blockMatVecMul_blockMatMul (A B : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (Ch02.blockMatMul A B) X =
      blockMatVecMul A (blockMatVecMul B X) := by
  refine Prod.ext ?_ ?_ <;>
    simp only [blockMatVecMul, Ch02.blockMatMul, matVecMul_add, add_matVecMul,
      ← matVecMul_mul] <;>
    abel

/-! ## Symmetry and positivity -/

/-- The action of a scalar block diagonal on a doubled vector. -/
theorem blockMatVecMul_blockDiag_smul_one (a b : ℝ) (X : BlockVec d) :
    blockMatVecMul (Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) X =
      (a • X.1, b • X.2) := by
  rw [blockMatVecMul]
  simp [Ch02.blockDiag, matVecMul_smul_one, zero_matVecMul]

/-- The doubled quadratic form of a scalar block diagonal. -/
theorem blockVecDot_blockMatVecMul_blockDiag_smul_one (a b : ℝ) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) X) =
      a * vecNormSq X.1 + b * vecNormSq X.2 := by
  rw [blockMatVecMul_blockDiag_smul_one, blockVecDot, vecDot_smul_right,
    vecDot_smul_right]
  rfl

/-! ## The inverse square root acting on a doubled load -/

/-- The inverse square root acts on a doubled load by the two scalar loads of
`Observable.inverseSqrtLoad` and `Observable.sqrtLoad`. -/
theorem blockMatVecMul_annealedLimitBlockInvSqrt (sigma : PositiveScalar)
    (u v : Vec d) :
    blockMatVecMul (annealedLimitBlockInvSqrt (d := d) sigma) (u, v) =
      (inverseSqrtLoad sigma u, sqrtLoad sigma v) := by
  rw [annealedLimitBlockInvSqrt, blockMatVecMul_blockDiag_smul_one]
  rfl

/-- The square root acts on a doubled load by the two scalar loads, swapped. -/
theorem blockMatVecMul_annealedLimitBlockSqrt (sigma : PositiveScalar)
    (u v : Vec d) :
    blockMatVecMul (annealedLimitBlockSqrt (d := d) sigma) (u, v) =
      (sqrtLoad sigma u, inverseSqrtLoad sigma v) := by
  rw [annealedLimitBlockSqrt, blockMatVecMul_blockDiag_smul_one]
  rfl

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
