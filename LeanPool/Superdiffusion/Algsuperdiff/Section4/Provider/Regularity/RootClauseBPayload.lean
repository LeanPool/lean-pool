/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepNineOffGridGeometry

/-!
# RootClauseBPayload

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- The producer's `v`-binder is met by the root's own `x ∈ □_m`. -/
theorem offGridLatticeIndex_mem_of_mem_cube {m : ℤ} (n : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) :
    offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
  offGridLatticeIndex_mem_latticeCubeSet n hx

end

end Algsuperdiff.Section4.Provider.Regularity
