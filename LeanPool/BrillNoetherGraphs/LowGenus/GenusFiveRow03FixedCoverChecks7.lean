/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.PairedCoverReplay
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck

/-! # Kernel replay batch 7 for the independent row-03 cover

A bounded batch keeps earlier reductions out of later kernel checks.
The original cover module retains its existing declarations and auxiliary proofs. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities
open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

namespace ReplayChecks7

attribute [local instance 2000] CompactCellTree.decidableCheckPairedKernel

theorem treePart60_check_paired :
    treePart60.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart60_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart60_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart60_check_paired

theorem treePart61_check_paired :
    treePart61.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart61_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart61_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart61_check_paired

theorem treePart62_check_paired :
    treePart62.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart62_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart62_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart62_check_paired

theorem treePart63_check_paired :
    treePart63.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart63_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart63_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart63_check_paired

theorem treePart64_check_paired :
    treePart64.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++
      [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

theorem treePart64_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart64_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart64_check_paired

theorem treePart65_check_paired :
    treePart65.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart65_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart65_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart65_check_paired

theorem treePart66_check_paired :
    treePart66.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart66_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart66_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart66_check_paired

theorem treePart67_check_paired :
    treePart67.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart67_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart67_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart67_check_paired

theorem treePart68_check_paired :
    treePart68.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0,
      0, 0])]) = true := by
  decide +kernel

theorem treePart68_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart68_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart68_check_paired

theorem treePart69_check_paired :
    treePart69.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart69_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart69_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart69_check_paired

theorem treePart70_check_paired :
    treePart70.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart70_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart70_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart70_check_paired

theorem treePart71_check_paired :
    treePart71.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

theorem treePart71_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart71_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart71_check_paired

theorem treePart72_check_paired :
    treePart72.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart72_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart72_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart72_check_paired

theorem treePart73_check_paired :
    treePart73.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  decide +kernel

theorem treePart73_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart73_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart73_check_paired

theorem treePart74_check_paired :
    treePart74.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) =
      true := by
  decide +kernel

theorem treePart74_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart74_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart74_check_paired

theorem treePart75_check_paired :
    treePart75.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart75_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart75_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart75_check_paired

theorem treePart76_check_paired :
    treePart76.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart76_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart76_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart76_check_paired

theorem treePart77_check_paired :
    treePart77.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart77_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart77_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart77_check_paired

theorem treePart78_check_paired :
    treePart78.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart78_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart78_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart78_check_paired

theorem treePart79_check_paired :
    treePart79.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])])
      = true := by
  decide +kernel

theorem treePart79_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart79_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart79_check_paired

theorem treePart80_check_paired :
    treePart80.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart80_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart80_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart80_check_paired

theorem treePart81_check_paired :
    treePart81.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart81_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart81_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart81_check_paired

theorem treePart82_check_paired :
    treePart82.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart82_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart82_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart82_check_paired

theorem treePart83_check_paired :
    treePart83.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart83_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart83_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart83_check_paired

end ReplayChecks7

end AtanasovRanganathan.GenusFiveRow03FixedCover
