/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryPoincareCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryTraceMeasure

/-!
# BoundaryWindowPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The translated open cube as an axis cube

The boundary branch of the general clause works on the anchor's own window
`W' = (z + □_{n+3}) ∩ □_m`, under the gate

```text
  (z + □_{n+2}) ∩ ∂□_m ≠ ∅ .
```

Every geometric reading of that window goes through one normal form, proved
here: a translated open triadic cube is the axis-parallel box of its own corner
and side, and membership in either description is the coordinatewise strict
inequality.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The translated open cube as an axis cube -/

/-- Membership in a translated open triadic cube, coordinatewise. -/
theorem mem_image_add_openCubeSet_iff {j : ℤ} {z y : Vec d} :
    y ∈ (fun y' => z + y') '' openCubeSet (originCube d j) ↔
      ∀ i, (-(1 / 2 : ℝ)) * (3 : ℝ) ^ j < y i - z i ∧
        y i - z i < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro i
    simpa using mem_openCubeSet_originCube_iff.mp hw i
  · intro h
    refine ⟨y - z, mem_openCubeSet_originCube_iff.mpr ?_, ?_⟩
    · intro i
      simpa using h i
    · funext i
      simp

/-- Membership in an axis cube, coordinatewise. -/
theorem mem_axisCube_iff {c : Vec d} {L : ℝ} {y : Vec d} :
    y ∈ axisCube c L ↔ ∀ j, c j < y j ∧ y j < c j + L := by
  simp [axisCube, Set.mem_pi, Set.mem_Ioo]

theorem image_add_openCubeSet_eq_axisCube (z : Vec d) (j : ℤ) :
    (fun y' => z + y') '' openCubeSet (originCube d j) =
      axisCube (fun i => z i - (1 / 2 : ℝ) * (3 : ℝ) ^ j) ((3 : ℝ) ^ j) := by
  ext y
  rw [mem_image_add_openCubeSet_iff, mem_axisCube_iff]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay
