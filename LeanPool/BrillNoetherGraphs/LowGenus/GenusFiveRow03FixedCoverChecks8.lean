/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! # Kernel replay batch 8 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks8

theorem treePart84_check_chunked :
    treePart84.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart85_check_chunked :
    treePart85.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart86_check_chunked :
    treePart86.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true
      := by
  decide +kernel

theorem treePart87_check_chunked :
    treePart87.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart88_check_chunked :
    treePart88.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart89_check_chunked :
    treePart89.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart90_check_chunked :
    treePart90.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1,
      0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart91_check_chunked :
    treePart91.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart92_check_chunked :
    treePart92.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart93_check_chunked :
    treePart93.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart94_check_chunked :
    treePart94.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++
      [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart95_check_chunked :
    treePart95.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart96_check_chunked :
    treePart96.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1,
      0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart97_check_chunked :
    treePart97.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true
      := by
  decide +kernel

theorem treePart98_check_chunked :
    treePart98.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart99_check_chunked :
    treePart99.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) =
      true := by
  decide +kernel

theorem treePart100_check_chunked :
    treePart100.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart101_check_chunked :
    treePart101.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart102_check_chunked :
    treePart102.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, -1]]) = true := by
  decide +kernel

theorem treePart103_check_chunked :
    treePart103.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) = true
  := by
  decide +kernel

theorem treePart104_check_chunked :
    treePart104.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
      0, 0, 0])]) = true := by
  decide +kernel

theorem treePart105_check_chunked :
    treePart105.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true
  := by
  decide +kernel

theorem treePart106_check_chunked :
    treePart106.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0, 0, 0])]) = true := by
  decide +kernel

theorem treePart107_check_chunked :
    treePart107.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  decide +kernel

end ReplayChecks8

end AtanasovRanganathan.GenusFiveRow03FixedCover
