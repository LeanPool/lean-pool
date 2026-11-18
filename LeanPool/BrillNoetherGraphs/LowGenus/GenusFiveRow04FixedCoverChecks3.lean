/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup

/-! # Kernel replay batch 3 for the independent row-04 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow04CoverBase
open GenusFiveRow04Symmetry (Chamber chamber_covers)

namespace ReplayChecks3

theorem treePart72_check_chunked :
    treePart72.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  decide +kernel

theorem treePart73_check_chunked :
    treePart73.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1])]) = true := by
  decide +kernel

theorem treePart74_check_chunked :
    treePart74.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

theorem treePart75_check_chunked :
    treePart75.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart76_check_chunked :
    treePart76.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart77_check_chunked :
    treePart77.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart78_check_chunked :
    treePart78.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1,
      0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart79_check_chunked :
    treePart79.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff [0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart80_check_chunked :
    treePart80.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff [0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart81_check_chunked :
    treePart81.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff [0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0,
      1])]) = true := by
  decide +kernel

theorem treePart82_check_chunked :
    treePart82.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1])]) = true := by
  decide +kernel

theorem treePart83_check_chunked :
    treePart83.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart84_check_chunked :
    treePart84.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart85_check_chunked :
    treePart85.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart86_check_chunked :
    treePart86.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart87_check_chunked :
    treePart87.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart88_check_chunked :
    treePart88.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
      -1, 0, -1])]) = true := by
  decide +kernel

theorem treePart89_check_chunked :
    treePart89.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]]) ++ [aff
      [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart90_check_chunked :
    treePart90.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart91_check_chunked :
    treePart91.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart92_check_chunked :
    treePart92.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1,
      -1, 0, -1])]) = true := by
  decide +kernel

theorem treePart93_check_chunked :
    treePart93.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1])]) = true := by
  decide +kernel

theorem treePart94_check_chunked :
    treePart94.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart95_check_chunked :
    treePart95.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

end ReplayChecks3

end AtanasovRanganathan.GenusFiveRow04FixedCover
