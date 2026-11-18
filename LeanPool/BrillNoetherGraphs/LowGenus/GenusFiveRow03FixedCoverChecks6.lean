/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! # Kernel replay batch 6 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks6

theorem treePart36_check_chunked :
    treePart36.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart37_check_chunked :
    treePart37.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart38_check_chunked :
    treePart38.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

theorem treePart39_check_chunked :
    treePart39.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart40_check_chunked :
    treePart40.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart41_check_chunked :
    treePart41.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0,
      0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart42_check_chunked :
    treePart42.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart43_check_chunked :
    treePart43.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart44_check_chunked :
    treePart44.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true
  := by
  decide +kernel

theorem treePart45_check_chunked :
    treePart45.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart46_check_chunked :
    treePart46.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  decide +kernel

theorem treePart47_check_chunked :
    treePart47.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0,
      0, 0]]) = true := by
  decide +kernel

theorem treePart48_check_chunked :
    treePart48.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart49_check_chunked :
    treePart49.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0]]) = true := by
  decide +kernel

theorem treePart50_check_chunked :
    treePart50.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart51_check_chunked :
    treePart51.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0,
      0, 0])]) = true := by
  decide +kernel

theorem treePart52_check_chunked :
    treePart52.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart53_check_chunked :
    treePart53.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart54_check_chunked :
    treePart54.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart55_check_chunked :
    treePart55.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart56_check_chunked :
    treePart56.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart57_check_chunked :
    treePart57.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart58_check_chunked :
    treePart58.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart59_check_chunked :
    treePart59.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

end ReplayChecks6

end AtanasovRanganathan.GenusFiveRow03FixedCover
