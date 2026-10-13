/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CubeControlAggregate

/-!
# LocalControlBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From pointwise unit descendants to local cube controls

This module upgrades the finite-cover pointwise bound to the exact `sSup`
control used by the lower-tail summability argument.
-/

namespace Algsuperdiff.Section3.Cutoff

open Set
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

private theorem localCubeControl_le_of_pointwise
    (ell : ℤ) (j : ShellField d) (C : ℝ)
    (hC : ∀ x ∈ openCubeSet (originCube d ell),
      HCPolySupport.Book.Ch02.matrixOperatorNorm (j x) ≤ C)
    (hC_nonneg : 0 ≤ C) :
    localCubeControl ell j ≤ C := by
  unfold localCubeControl ShellField.unitCubeValueNorm
  apply csSup_le
  · exact ⟨0, none, rfl⟩
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact hC_nonneg
  | some x =>
      let r : ℝ := cubeScaleFactor (originCube d ell)
      have hx : r • x.1 ∈ openCubeSet (originCube d ell) := by
        rw [openCubeSet_originCube_eq_smul_originCube_zero, Set.mem_smul_set]
        exact ⟨x.1, x.2, rfl⟩
      change HCPolySupport.Book.Ch02.matrixOperatorNorm
          ((ShellField.spatialScale r j) x.1) ≤ C
      rw [ShellField.spatialScale_apply]
      exact hC _ hx

/-- The exact `sSup` local control on a nonnegative-scale origin cube is
bounded by the finite maximum of translated unit-cube controls. -/
theorem localCubeControl_le_originCubeUnitControlMax
    (q : ℤ) (hq : 0 ≤ q) (j : ShellField d) :
    localCubeControl q j ≤ originCubeUnitControlMax q hq j := by
  apply localCubeControl_le_of_pointwise q j
    (originCubeUnitControlMax q hq j)
  · intro x hx
    exact matrixOperatorNorm_le_originCubeUnitControlMax q hq j
      (openCubeSet_subset_cubeSet _ hx)
  · exact originCubeUnitControlMax_nonneg q hq j

/-- On a nonpositive-scale centered cube, the local control is bounded by the
unit-cube control. -/
theorem localCubeControl_le_localCubeControl_zero
    (q : ℤ) (hq : q ≤ 0) (j : ShellField d) :
    localCubeControl q j ≤ localCubeControl 0 j := by
  apply localCubeControl_le_of_pointwise q j (localCubeControl 0 j)
  · intro x hx
    have hr : cubeScaleFactor (originCube d q) ≤ 1 := by
      simpa [cubeScaleFactor_originCube] using
        (zpow_le_one_of_nonpos₀ (show (1 : ℝ) ≤ 3 by norm_num) hq)
    have hr' : (3 : ℝ) ^ q ≤ 1 := by
      simpa [cubeScaleFactor_originCube] using hr
    have hx0 : x ∈ openCubeSet (originCube d 0) := by
      rw [mem_openCubeSet_originCube_iff] at hx ⊢
      intro i
      rcases hx i with ⟨hlo, hhi⟩
      constructor
      · norm_num
        nlinarith [hr']
      · norm_num
        nlinarith [hr']
    let y : ShellField.UnitOpenCubePoint d := ⟨x, hx0⟩
    simpa only [localCubeControl_zero_eq_unitCubeValueNorm] using
      ShellField.matrixOperatorNorm_apply_le_unitCubeValueNorm j y
  · rw [localCubeControl_zero_eq_unitCubeValueNorm]
    exact ShellField.unitCubeValueNorm_nonneg j

end

end Algsuperdiff.Section3.Cutoff
