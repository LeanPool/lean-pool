/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.PairedCoverReplay
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

attribute [local instance 2000] CompactCellTree.decidableCheckPairedKernel

theorem treePart12_check_paired :
    treePart12.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]])
      ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart12_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart12_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart12_check_paired

theorem treePart13_check_paired :
    treePart13.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart13_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart13_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart13_check_paired

theorem treePart14_check_paired :
    treePart14.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart14_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart14_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart14_check_paired

theorem treePart15_check_paired :
    treePart15.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) = true := by
  decide +kernel

theorem treePart15_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart15_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart15_check_paired

theorem treePart16_check_paired :
    treePart16.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart16_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart16_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart16_check_paired

theorem treePart17_check_paired :
    treePart17.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart17_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart17_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart17_check_paired

theorem treePart18_check_paired :
    treePart18.checkPaired splitForms farkasReceiptLookup cells
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

theorem treePart18_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart18_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart18_check_paired

theorem treePart19_check_paired :
    treePart19.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart19_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart19_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart19_check_paired

theorem treePart20_check_paired :
    treePart20.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0,
      1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) =
      true := by
  decide +kernel

theorem treePart20_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart20_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart20_check_paired

theorem treePart21_check_paired :
    treePart21.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0,
      1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0,
      -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart21_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart21_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart21_check_paired

theorem treePart22_check_paired :
    treePart22.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart22_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart22_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart22_check_paired

theorem treePart23_check_paired :
    treePart23.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart23_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart23_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart23_check_paired

theorem treePart24_check_paired :
    treePart24.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true
  := by
  decide +kernel

theorem treePart24_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart24_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart24_check_paired

theorem treePart25_check_paired :
    treePart25.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart25_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart25_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart25_check_paired

theorem treePart26_check_paired :
    treePart26.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) = true := by
  decide +kernel

theorem treePart26_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart26_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart26_check_paired

theorem treePart27_check_paired :
    treePart27.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart27_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart27_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart27_check_paired

theorem treePart28_check_paired :
    treePart28.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart28_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart28_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart28_check_paired

theorem treePart29_check_paired :
    treePart29.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart29_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart29_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart29_check_paired

theorem treePart30_check_paired :
    treePart30.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart30_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart30_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart30_check_paired

theorem treePart31_check_paired :
    treePart31.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart31_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart31_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart31_check_paired

theorem treePart32_check_paired :
    treePart32.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1])]) = true := by
  decide +kernel

theorem treePart32_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart32_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart32_check_paired

theorem treePart33_check_paired :
    treePart33.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart33_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart33_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart33_check_paired

theorem treePart34_check_paired :
    treePart34.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart34_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart34_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart34_check_paired

theorem treePart35_check_paired :
    treePart35.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart35_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart35_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart35_check_paired

end ReplayChecks5

end AtanasovRanganathan.GenusFiveRow03FixedCover
