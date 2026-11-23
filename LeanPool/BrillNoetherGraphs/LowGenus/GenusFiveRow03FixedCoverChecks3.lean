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

/-! # Kernel replay batch 3 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks3

attribute [local instance 2000] CertificateData.decidableCheckClosedRows

theorem cell72_check_indexed : cell72.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 17, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell73_check_indexed : cell73.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  decide +kernel

theorem cell74_check_indexed : cell74.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  decide +kernel

theorem cell75_check_indexed : cell75.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 17, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell76_check_indexed : cell76.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 17, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell77_check_indexed : cell77.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  decide +kernel

theorem cell78_check_indexed : cell78.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  decide +kernel

theorem cell79_check_indexed : cell79.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  decide +kernel

theorem cell80_check_indexed : cell80.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  decide +kernel

theorem cell81_check_indexed : cell81.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  decide +kernel

theorem cell82_check_indexed : cell82.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  decide +kernel

theorem cell83_check_indexed : cell83.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  decide +kernel

theorem cell84_check_indexed : cell84.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell85_check_indexed : cell85.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 17, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell86_check_indexed : cell86.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  decide +kernel

theorem cell87_check_indexed : cell87.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  decide +kernel

theorem cell88_check_indexed : cell88.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 17, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  decide +kernel

theorem cell89_check_indexed : cell89.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  decide +kernel

theorem cell90_check_indexed : cell90.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  decide +kernel

theorem cell91_check_indexed : cell91.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  decide +kernel

theorem cell92_check_indexed : cell92.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

theorem cell93_check_indexed : cell93.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

theorem cell94_check_indexed : cell94.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

theorem cell95_check_indexed : cell95.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

end ReplayChecks3

end AtanasovRanganathan.GenusFiveRow03FixedCover
