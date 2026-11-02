/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootInterfaceGate
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoveringSlotObstruction

/-!
# StepSevenCaccBoundaryGate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 0. Triadic arithmetic -/

/-- Half a triadic side is positive. -/
theorem half_three_zpow_pos' (j : ℤ) : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  linarith only [h3]

/-! ## 1. The positive half: the clamped outer cube at the sharp gate -/

/-- **The clamped outer cube sits inside the next window up.**  This is where the
right-hand side of the boundary `hcacc` is read: `c + □_j ⊆ U_{j+1}`. -/
theorem image_add_wellPlacedCentre_subset_truncatedWindow_succ {m j : ℤ}
    (hjm : j ≤ m) {z : Vec d} (hz : z ∈ openCubeSet (originCube d m)) :
    (fun y => wellPlacedCentre z m j + y) '' openCubeSet (originCube d j) ⊆
      truncatedWindow z m (j + 1) := by
  have hzz : z - z ∈ openCubeSet (originCube d (j - 1)) := by
    rw [sub_self, mem_openCubeSet_originCube_iff]
    intro i
    have h := half_three_zpow_pos' (j - 1)
    exact ⟨by simp only [Pi.zero_apply]; linarith only [h],
      by simp only [Pi.zero_apply]; linarith only [h]⟩
  have hin := image_add_wellPlacedCentre_subset_image_add_openCubeSet_succ
    (k := j) (m := m) (x := z) (z := z) hjm hz hzz
  exact Set.subset_inter hin (image_add_wellPlacedCentre_subset_openCubeSet z hjm)

end

end Algsuperdiff.Section4.Provider.Regularity
