/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import LeanPool.MovingSofa.Gerver.Foundations.Development002
/-!
# Optimality from the area upper bound

`AreaUpperBound` says that no moving sofa has larger area than Gerver's sofa. Since Gerver's sofa
is itself a moving sofa, the bound gives `sofaConstant = volume gerversSofa`.
-/

@[expose] public section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry unitInterval

/-- Every moving sofa has area at most that of Gerver's sofa. This is the upper bound proved in
Baek's paper; together with the fact that Gerver's sofa is a moving sofa it gives optimality. -/
def AreaUpperBound : Prop :=
  ∀ (s : Set ℝ²) (m : I → E(2)), IsMovingSofa s m → volume s ≤ volume gerversSofa

/-- The area upper bound implies that Gerver's sofa attains the sofa constant. -/
theorem optimality_of_areaUpperBound (h : AreaUpperBound) :
    sofaConstant = volume gerversSofa := by
  apply le_antisymm _ volume_gerversSofa_le_sofaConstant
  unfold sofaConstant
  refine iSup_le fun s ↦ iSup_le fun hs ↦ ?_
  obtain ⟨m, hm⟩ := hs
  exact h s m hm

end MovingSofa
