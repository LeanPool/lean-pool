/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CubeControlCover

/-!
# CubeControlBoundary

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Boundary extension for translated unit-cube controls

The J2 observable controls a literal open cube.  Since shell fields are
continuous, this module extends that control to the canonical half-open cube
used by triadic partitions.
-/

namespace Algsuperdiff.Section3.Cutoff

open Set
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- A canonical half-open triadic cube lies in the closure of its open
counterpart. -/
theorem cubeSet_subset_closure_openCubeSet (Q : TriadicCube d) :
    cubeSet Q ⊆ closure (openCubeSet Q) := by
  rw [cubeSet_eq_pi_Ico, openCubeSet_eq_pi_Ioo, closure_pi_set]
  intro x hx i hi
  change x i ∈ closure (Set.Ioo
    (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
    (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))
  rw [closure_Ioo]
  · exact ⟨(hx i hi).1, (hx i hi).2.le⟩
  · have hpos : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    nlinarith

/-- The continuous matrix operator norm is bounded by the translated unit
control on the whole half-open unit cube. -/
theorem matrixOperatorNorm_le_translatedUnitCubeControl_of_mem_cubeSet
    (R : TriadicCube d) (hR : R.scale = 0) (j : ShellField d) {x : Vec d}
    (hx : x ∈ cubeSet R) :
    HCPolySupport.Book.Ch02.matrixOperatorNorm (j x) ≤
      translatedUnitCubeControl (triadicCubeShift R) j := by
  let f : Vec d → ℝ := fun y => HCPolySupport.Book.Ch02.matrixOperatorNorm (j y)
  have hcont : Continuous f :=
    ShellField.continuous_matrixOperatorNorm.comp j.1.1.continuous
  have hclosed : IsClosed (f ⁻¹' Set.Iic
      (translatedUnitCubeControl (triadicCubeShift R) j)) :=
    isClosed_Iic.preimage hcont
  have hopen : openCubeSet R ⊆ f ⁻¹' Set.Iic
      (translatedUnitCubeControl (triadicCubeShift R) j) := by
    intro y hy
    have hy' : y ∈ translateSet (triadicCubeShift R)
        (openCubeSet (originCube d 0)) := by
      rw [← hR, ← openCubeSet_eq_translateSet_originCube_of_triadicCube R]
      exact hy
    exact matrixOperatorNorm_le_translatedUnitCubeControl _ _ hy'
  have hx' : x ∈ closure (openCubeSet R) :=
    cubeSet_subset_closure_openCubeSet R hx
  exact hclosed.closure_subset (closure_mono hopen hx')

end

end Algsuperdiff.Section3.Cutoff
