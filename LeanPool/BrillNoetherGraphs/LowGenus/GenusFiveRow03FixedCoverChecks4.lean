/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! # Kernel replay batch 4 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks4

theorem cell96_check_indexed : cell96.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  decide +kernel

theorem cell97_check_indexed : cell97.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 17, 15, 15, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

theorem cell98_check_indexed : cell98.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 17, 15, 15, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

theorem cell99_check_indexed : cell99.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  decide +kernel

theorem cell100_check_indexed : cell100.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  decide +kernel

theorem cell101_check_indexed : cell101.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

theorem cell102_check_indexed : cell102.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 17, 15, 15, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

theorem cell103_check_indexed : cell103.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  decide +kernel

theorem cell104_check_indexed : cell104.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  decide +kernel

theorem cell105_check_indexed : cell105.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  decide +kernel

theorem cell106_check_indexed : cell106.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  decide +kernel

theorem cell107_check_indexed : cell107.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  decide +kernel

theorem treePart0_check_chunked :
    treePart0.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart1_check_chunked :
    treePart1.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0,
      0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true
      := by
  decide +kernel

theorem treePart2_check_chunked :
    treePart2.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0,
      0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart3_check_chunked :
    treePart3.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart4_check_chunked :
    treePart4.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart5_check_chunked :
    treePart5.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart6_check_chunked :
    treePart6.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart7_check_chunked :
    treePart7.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart8_check_chunked :
    treePart8.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) =
      true := by
  decide +kernel

theorem treePart9_check_chunked :
    treePart9.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart10_check_chunked :
    treePart10.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart11_check_chunked :
    treePart11.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      0])]) = true := by
  decide +kernel

end ReplayChecks4

end AtanasovRanganathan.GenusFiveRow03FixedCover
