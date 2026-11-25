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

/-! # Kernel replay batch 0 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks0

attribute [local instance 2000] CertificateData.decidableCheckClosedRowsIndexedKernel

theorem cell0_check_indexed : cell0.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 13, 14, 15], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 8, 16, 15, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 14]] = true := by
  decide +kernel

theorem cell1_check_indexed : cell1.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  decide +kernel

theorem cell2_check_indexed : cell2.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 18, 4, 0, 0, 0, 0, 0,
     0, 9, 19, 4, 20], [], [], [21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell3_check_indexed : cell3.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  decide +kernel

theorem cell4_check_indexed : cell4.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 4, 0, 0, 0, 0, 0,
     0, 9, 19, 4, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell5_check_indexed : cell5.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16, 21,
     22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell6_check_indexed : cell6.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  decide +kernel

theorem cell7_check_indexed : cell7.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21,
     0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell8_check_indexed : cell8.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell9_check_indexed : cell9.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0,
     0, 9, 19, 3, 20], [], [], [21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell10_check_indexed : cell10.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0,
     0, 9, 19, 3, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell11_check_indexed : cell11.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell12_check_indexed : cell12.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  decide +kernel

theorem cell13_check_indexed : cell13.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  decide +kernel

theorem cell14_check_indexed : cell14.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [14, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  decide +kernel

theorem cell15_check_indexed : cell15.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 4, 0, 0, 0, 0, 0,
     0, 9, 19, 4, 20], [], [], [14, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell16_check_indexed : cell16.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [20, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22,
     23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell17_check_indexed : cell17.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [20, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0,
     0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  decide +kernel

theorem cell18_check_indexed : cell18.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0,
     0, 9, 19, 3, 20], [], [], [14, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell19_check_indexed : cell19.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [20, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0,
     0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  decide +kernel

theorem cell20_check_indexed : cell20.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0,
     0, 9, 19, 3, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell21_check_indexed : cell21.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 16, 21,
     22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

theorem cell22_check_indexed : cell22.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  decide +kernel

theorem cell23_check_indexed : cell23.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16, 21,
     22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  decide +kernel

end ReplayChecks0

end AtanasovRanganathan.GenusFiveRow03FixedCover
