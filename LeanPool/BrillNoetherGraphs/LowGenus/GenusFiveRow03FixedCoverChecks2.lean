/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! # Kernel replay batch 2 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks2

theorem cell48_check_indexed : cell48.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 9, 16, 3, 19], [], [], [20, 16, 16, 14, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  decide +kernel

theorem cell49_check_indexed : cell49.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0,
     0, 0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 9, 16, 3, 19], [], [], [20, 16, 16, 21, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  decide +kernel

theorem cell50_check_indexed : cell50.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 9, 16, 3, 19], [], [], [14, 16, 16, 20, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  decide +kernel

theorem cell51_check_indexed : cell51.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell52_check_indexed : cell52.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell53_check_indexed : cell53.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell54_check_indexed : cell54.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 20, 15, 20, 15, 1, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell55_check_indexed : cell55.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 13, 14, 15], [0, 0, 0, 0, 16, 8, 8, 17,
     0, 0, 0, 0, 9, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 14]] = true := by
  decide +kernel

theorem cell56_check_indexed : cell56.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  decide +kernel

theorem cell57_check_indexed : cell57.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  decide +kernel

theorem cell58_check_indexed : cell58.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 13, 14, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 9, 14, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 14]] = true := by
  decide +kernel

theorem cell59_check_indexed : cell59.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 13, 14, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 9, 14, 3, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 14]] = true := by
  decide +kernel

theorem cell60_check_indexed : cell60.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 9, 16, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21,
     22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]] = true := by
  decide +kernel

theorem cell61_check_indexed : cell61.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8,
     18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 19], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 20]] = true := by
  decide +kernel

theorem cell62_check_indexed : cell62.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 8, 16, 15, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17]] = true := by
  decide +kernel

theorem cell63_check_indexed : cell63.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 8, 16, 15, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17]] = true := by
  decide +kernel

theorem cell64_check_indexed : cell64.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8,
     18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 19], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 20]] = true := by
  decide +kernel

theorem cell65_check_indexed : cell65.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 8, 17, 18, 19], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 7, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell66_check_indexed : cell66.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 8, 16, 15, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17]] = true := by
  decide +kernel

theorem cell67_check_indexed : cell67.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell68_check_indexed : cell68.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell69_check_indexed : cell69.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 17, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell70_check_indexed : cell70.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  decide +kernel

theorem cell71_check_indexed : cell71.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  decide +kernel

end ReplayChecks2

end AtanasovRanganathan.GenusFiveRow03FixedCover
