/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! # Kernel replay batch 5 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks5

theorem treePart12_check_chunked :
    treePart12.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]])
      ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart13_check_chunked :
    treePart13.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart14_check_chunked :
    treePart14.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart15_check_chunked :
    treePart15.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) = true := by
  decide +kernel

theorem treePart16_check_chunked :
    treePart16.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart17_check_chunked :
    treePart17.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart18_check_chunked :
    treePart18.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1])]) = true := by
  decide +kernel

theorem treePart19_check_chunked :
    treePart19.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart20_check_chunked :
    treePart20.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0,
      1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) =
      true := by
  decide +kernel

theorem treePart21_check_chunked :
    treePart21.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0,
      1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0,
      -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart22_check_chunked :
    treePart22.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart23_check_chunked :
    treePart23.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart24_check_chunked :
    treePart24.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true
  := by
  decide +kernel

theorem treePart25_check_chunked :
    treePart25.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart26_check_chunked :
    treePart26.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) = true := by
  decide +kernel

theorem treePart27_check_chunked :
    treePart27.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart28_check_chunked :
    treePart28.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart29_check_chunked :
    treePart29.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart30_check_chunked :
    treePart30.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart31_check_chunked :
    treePart31.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart32_check_chunked :
    treePart32.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1])]) = true := by
  decide +kernel

theorem treePart33_check_chunked :
    treePart33.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart34_check_chunked :
    treePart34.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart35_check_chunked :
    treePart35.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

end ReplayChecks5

end AtanasovRanganathan.GenusFiveRow03FixedCover
