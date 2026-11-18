/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! # Kernel replay batch 10 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks10

theorem treePart132_check_chunked :
    treePart132.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      0, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart133_check_chunked :
    treePart133.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1])]) = true := by
  decide +kernel

end ReplayChecks10

end AtanasovRanganathan.GenusFiveRow03FixedCover
