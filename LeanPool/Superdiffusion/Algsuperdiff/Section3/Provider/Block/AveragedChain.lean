/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Block.AveragedBlock
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Block.CompletedSquares
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.PotentialSolenoidal
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMu
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# AveragedChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the averaged block chain `e.CG.bounds.2`

This file proves a local version of the right-hand inequality of the display
`e.CG.bounds.2` in ABK26,

`(⨍_U bfA⁻¹(x) dx)⁻¹ ≤ bfA_*(U) ≤ bfA(U) ≤ ⨍_U bfA(x) dx`,

for an admissible block coefficient field on a Chapter 2 domain, in the doubled
Loewner order `Homogenization.BlockMatLoewnerLE`.

The inequality is proved by the variational route of the notes, and is
accompanied by the order isomorphism that turns it into the left-hand bound.

* **Right, `bfA(U) ≤ ⨍_U bfA`.**  The constant doubled field `x ↦ P` is
  admissible for the doubled `mu` problem at load `P` (its fluctuation is zero),
  so the minimum `mu(U,P)` is at most the energy of that competitor, which is
  `½ P ⬝ (⨍_U bfA) P` by
  `average_blockEnergyDensityAt`.  On the other side
  `Book.Ch02.DoubledMuTheory.mu_quadratic` identifies `mu(U,P) = ½ P ⬝ bfA(U) P`.

* **Reflection.**  In the doubled formalism the pointwise inverse is the block
  reflection, `bfA⁻¹(x) = blockReflect (bfA(x))`, exactly as
  `bfA_*⁻¹(U) = blockReflect (bfA(U))` at the coarse level.  Reflection is an
  order isomorphism for the doubled Loewner order
  (`blockMatLoewnerLE_blockReflect`), so the dual form of the left-hand bound —
  `bfA_*⁻¹(U) ≤ ⨍_U bfA⁻¹(x) dx`, the form that does not invert a matrix — is
  the block reflection of the right-hand bound.
-/

namespace Algsuperdiff.Section3.Provider.Block

open HCPolySupport HCPolySupport.Book.Ch02

variable {d : ℕ}

/-! ## Right inequality: `bfA(U) ≤ ⨍_U bfA(x) dx` -/

/-- The constant doubled field at load `P` is admissible for the doubled `mu`
problem at load `P`: its fluctuation vanishes identically. -/
theorem isDoubledMuAdmissible_const (U : Domain d) (P : BlockVec d) :
    IsDoubledMuAdmissible U P { potential := fun _ => P.1, flux := fun _ => P.2 } := by
  constructor
  · have hzero : (fun x => (fun _ : Vec d => P.1) x - P.1) = (0 : Vec d → Vec d) := by
      funext x
      simp
    rw [hzero]
    exact Book.Ch01.potentialZeroTraceFieldOn_of_h10 (0 : H10Function (U : Set (Vec d)))
  · have hzero : (fun x => (fun _ : Vec d => P.2) x - P.2) = (0 : Vec d → Vec d) := by
      funext x
      simp
    rw [hzero]
    refine ⟨MeasureTheory.MemLp.zero, ?_⟩
    intro phi
    simp [vecDot]

/-- `e.CG.bounds.2`, right inequality: the coarse block matrix is dominated by the
volume average of the pointwise doubled coefficient matrix. -/
theorem coarseBlockMatrix_blockMatLoewnerLE_averagedBlockMatrix
    (U : Domain d) (a : CoeffOn U) :
    BlockMatLoewnerLE (Book.Ch02.coarseBlockMatrix U a) (averagedBlockMatrix U a) := by
  intro X
  obtain ⟨X0, hX0⟩ := (doubledMuTheory U a).minimizer_exists X
  have hmin : doubledMuValue U a X0 = doubledMu U a X :=
    hX0.doubledMuValue_eq_doubledMu
  have hle :
      doubledMuValue U a X0 ≤
        doubledMuValue U a { potential := fun _ => X.1, flux := fun _ => X.2 } :=
    hX0.2 _ (isDoubledMuAdmissible_const U X)
  have hquad : doubledMu U a X =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) X) :=
    (doubledMuTheory U a).mu_quadratic X
  have hconst :
      doubledMuValue U a { potential := fun _ => X.1, flux := fun _ => X.2 } =
        (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (averagedBlockMatrix U a) X) :=
    average_blockEnergyDensityAt U a X
  rw [hmin, hquad, hconst] at hle
  exact hle

end Algsuperdiff.Section3.Provider.Block
