/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! # Kernel replay batch 9 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks9

theorem treePart108_check_chunked :
    treePart108.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      -1])]) = true := by
  decide +kernel

theorem treePart109_check_chunked :
    treePart109.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0,
      0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart110_check_chunked :
    treePart110.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart111_check_chunked :
    treePart111.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0,
      0, 1, 0, 0, 0, -1, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart112_check_chunked :
    treePart112.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart113_check_chunked :
    treePart113.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart114_check_chunked :
    treePart114.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart115_check_chunked :
    treePart115.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart116_check_chunked :
    treePart116.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0,
      1, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart117_check_chunked :
    treePart117.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart118_check_chunked :
    treePart118.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0,
      0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart119_check_chunked :
    treePart119.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0,
      1, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart120_check_chunked :
    treePart120.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart121_check_chunked :
    treePart121.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart122_check_chunked :
    treePart122.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart123_check_chunked :
    treePart123.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      = true := by
  decide +kernel

theorem treePart124_check_chunked :
    treePart124.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart125_check_chunked :
    treePart125.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart126_check_chunked :
    treePart126.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart127_check_chunked :
    treePart127.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart128_check_chunked :
    treePart128.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0,
      0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart129_check_chunked :
    treePart129.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true
  := by
  decide +kernel

theorem treePart130_check_chunked :
    treePart130.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart131_check_chunked :
    treePart131.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0,
      0, 0, 1])]) = true := by
  decide +kernel

end ReplayChecks9

end AtanasovRanganathan.GenusFiveRow03FixedCover
