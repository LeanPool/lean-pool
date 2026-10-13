/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.AxisCube

/-!
# CubeAxisBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The translated triadic cube as an axis cube

The localized Dirichlet problems are indexed by the translated triadic cube
`cubeSetAt y n`, the open cube of side `3 ^ n` centred at `y`, while the
boundary regularity theory is stated for the axis cube `axisCube z L`, the
open box `z + (0, L) ^ d`.  The two carriers agree once the centre is
converted into the lower corner.

The other hypothesis the variational theory asks of this carrier,
`IsOpenBoundedConvexDomain (cubeSetAt y n)`, is already available as
`isOpenBoundedConvexDomain_cubeSetAt`; it is recorded here as the sole
remaining geometric input of the whole-space comparison on a triadic cube.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport

variable {d : ℕ}

/-- **The translated triadic cube is an axis cube.**  Its lower corner is the
centre shifted by half the side length. -/
theorem cubeSetAt_eq_axisCube (y : Vec d) (n : ℤ) :
    cubeSetAt y n = axisCube (fun i => y i - (3 : ℝ) ^ n / 2) ((3 : ℝ) ^ n) := by
  ext x
  rw [mem_cubeSetAt_iff_forall_coord]
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioo]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩

end Algsuperdiff.Section5.Support
