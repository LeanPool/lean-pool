/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.PairedCoverReplay
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

attribute [local instance 2000] CompactCellTree.decidableCheckPairedKernel

theorem treePart108_check_paired :
    treePart108.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      -1])]) = true := by
  decide +kernel

theorem treePart108_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart108_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart108_check_paired

theorem treePart109_check_paired :
    treePart109.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0,
      0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart109_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart109_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart109_check_paired

theorem treePart110_check_paired :
    treePart110.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart110_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart110_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart110_check_paired

theorem treePart111_check_paired :
    treePart111.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0,
      0, 1, 0, 0, 0, -1, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart111_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart111_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart111_check_paired

theorem treePart112_check_paired :
    treePart112.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart112_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart112_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart112_check_paired

theorem treePart113_check_paired :
    treePart113.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart113_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart113_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart113_check_paired

theorem treePart114_check_paired :
    treePart114.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart114_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart114_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart114_check_paired

theorem treePart115_check_paired :
    treePart115.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart115_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart115_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart115_check_paired

theorem treePart116_check_paired :
    treePart116.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0,
      1, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart116_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart116_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart116_check_paired

theorem treePart117_check_paired :
    treePart117.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart117_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart117_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart117_check_paired

theorem treePart118_check_paired :
    treePart118.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0,
      0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart118_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart118_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart118_check_paired

theorem treePart119_check_paired :
    treePart119.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0,
      1, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart119_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart119_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart119_check_paired

theorem treePart120_check_paired :
    treePart120.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart120_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart120_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart120_check_paired

theorem treePart121_check_paired :
    treePart121.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart121_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart121_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart121_check_paired

theorem treePart122_check_paired :
    treePart122.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart122_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart122_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart122_check_paired

theorem treePart123_check_paired :
    treePart123.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      = true := by
  decide +kernel

theorem treePart123_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart123_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart123_check_paired

theorem treePart124_check_paired :
    treePart124.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart124_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart124_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart124_check_paired

theorem treePart125_check_paired :
    treePart125.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart125_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart125_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart125_check_paired

theorem treePart126_check_paired :
    treePart126.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart126_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart126_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart126_check_paired

theorem treePart127_check_paired :
    treePart127.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart127_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart127_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart127_check_paired

theorem treePart128_check_paired :
    treePart128.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0,
      0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart128_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart128_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart128_check_paired

theorem treePart129_check_paired :
    treePart129.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true
  := by
  decide +kernel

theorem treePart129_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart129_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart129_check_paired

theorem treePart130_check_paired :
    treePart130.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart130_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart130_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart130_check_paired

theorem treePart131_check_paired :
    treePart131.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0,
      0, 0, 1])]) = true := by
  decide +kernel

theorem treePart131_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart131_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart131_check_paired

end ReplayChecks9

end AtanasovRanganathan.GenusFiveRow03FixedCover
