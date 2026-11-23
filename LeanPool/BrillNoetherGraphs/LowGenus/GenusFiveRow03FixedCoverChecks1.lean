/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck
import LeanPool.BrillNoetherGraphs.LowGenus.IndexedCellReplay

/-! # Kernel replay batch 1 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks1

attribute [local instance 2000] CertificateData.decidableCheckClosedRows

theorem cell24_check_indexed : cell24.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell25_check_indexed : cell25.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  decide +kernel

theorem cell26_check_indexed : cell26.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  decide +kernel

theorem cell27_check_indexed : cell27.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell28_check_indexed : cell28.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21,
     0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell29_check_indexed : cell29.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell30_check_indexed : cell30.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell31_check_indexed : cell31.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 13, 14, 15, 16], [0,
     0, 0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [20, 19, 19, 21, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]]
     = true := by
  decide +kernel

theorem cell32_check_indexed : cell32.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 18, 8, 8, 19, 0, 0, 0, 0, 9, 16], [], [], [20, 16, 16, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]] = true := by
  decide +kernel

theorem cell33_check_indexed : cell33.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0,
     0, 0, 0, 18, 8, 8, 19, 0, 0, 0, 0, 9, 16], [], [], [20, 16, 16, 21, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  decide +kernel

theorem cell34_check_indexed : cell34.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 18, 8, 8, 19, 0, 0, 0, 0, 9, 16], [], [], [14, 16, 16, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]] = true := by
  decide +kernel

theorem cell35_check_indexed : cell35.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 13, 14, 15, 16], [0,
     0, 0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [20, 18, 18, 21, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell36_check_indexed : cell36.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 18, 4, 0, 0, 0, 0, 0, 0, 9, 16, 4, 19], [], [], [20, 16, 16, 14, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  decide +kernel

theorem cell37_check_indexed : cell37.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0,
     0, 0, 0, 18, 4, 0, 0, 0, 0, 0, 0, 9, 16, 4, 19], [], [], [20, 16, 16, 21, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  decide +kernel

theorem cell38_check_indexed : cell38.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 18, 4, 0, 0, 0, 0, 0, 0, 9, 16, 4, 19], [], [], [14, 16, 16, 20, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  decide +kernel

theorem cell39_check_indexed : cell39.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell40_check_indexed : cell40.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell41_check_indexed : cell41.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell42_check_indexed : cell42.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell43_check_indexed : cell43.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell44_check_indexed : cell44.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 20, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell45_check_indexed : cell45.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 15, 20, 15, 1, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell46_check_indexed : cell46.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 20, 15, 20, 15, 1, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell47_check_indexed : cell47.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 13, 14, 15, 16], [0,
     0, 0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [20, 18, 18, 21, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

end ReplayChecks1

end AtanasovRanganathan.GenusFiveRow03FixedCover
