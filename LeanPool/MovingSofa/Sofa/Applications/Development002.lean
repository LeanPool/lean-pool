/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Motion.Applications.Development001
/-!
# Moving sofa: related mathematical developments

* `Sofa.BalancedRightAngle`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Sofa / Balanced Right Angle
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem exists_dominating_balancedRightAngleSofa (s : Set Point)
    (hs : IsPaperMovingSofa s) (harea : (11 : ℝ) / 5 ≤ ClassicalResults.area s) :
    ∃ s' : Set Point, IsBalancedMaximumSofa s' (Real.pi / 2) ∧
      ClassicalResults.area s ≤ ClassicalResults.area s' := by
  obtain ⟨ω, hω, hrot⟩ := movingSofa_rotationAngle_bound s hs harea
  have hω0 : 0 < ω := lt_of_lt_of_le (Real.arccos_pos.2 (by norm_num)) hω.1
  obtain ⟨K, -, hBsofa, hBmax⟩ := exists_balancedMaximumSofa ω hω0 hω.2
  have hsB : ClassicalResults.area s ≤
      ClassicalResults.area ((K.val : Set Point) \ capNiche K) := hBmax s hrot
  obtain ⟨α, hrotB⟩ := balancedMaximumSofa_rightAngle _ ω hBsofa hω (harea.trans hsB)
  obtain ⟨K', -, hS'sofa, hS'max⟩ :=
    exists_balancedMaximumSofa (Real.pi / 2) (by positivity) le_rfl
  refine ⟨(K'.val : Set Point) \ capNiche K', hS'sofa, hsB.trans ?_⟩
  calc ClassicalResults.area ((K.val : Set Point) \ capNiche K)
      = ClassicalResults.area (rotationMap α '' ((K.val : Set Point) \ capNiche K)) :=
        (area_image_rotationMap α _).symm
    _ ≤ _ := hS'max _ hrotB

end MovingSofa

end

end

end
