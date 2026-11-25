/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.PairedCoverReplay
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

attribute [local instance 2000] CompactCellTree.decidableCheckPairedKernel

theorem treePart36_check_paired :
    treePart36.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart36_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart36_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart36_check_paired

theorem treePart37_check_paired :
    treePart37.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart37_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart37_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart37_check_paired

theorem treePart38_check_paired :
    treePart38.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

theorem treePart38_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart38_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart38_check_paired

theorem treePart39_check_paired :
    treePart39.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart39_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart39_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart39_check_paired

theorem treePart40_check_paired :
    treePart40.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart40_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart40_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart40_check_paired

theorem treePart41_check_paired :
    treePart41.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0,
      0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart41_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart41_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart41_check_paired

theorem treePart42_check_paired :
    treePart42.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart42_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart42_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart42_check_paired

theorem treePart43_check_paired :
    treePart43.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart43_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart43_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart43_check_paired

theorem treePart44_check_paired :
    treePart44.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true
  := by
  decide +kernel

theorem treePart44_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart44_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart44_check_paired

theorem treePart45_check_paired :
    treePart45.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart45_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart45_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart45_check_paired

theorem treePart46_check_paired :
    treePart46.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  decide +kernel

theorem treePart46_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart46_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart46_check_paired

theorem treePart47_check_paired :
    treePart47.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0,
      0, 0]]) = true := by
  decide +kernel

theorem treePart47_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart47_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart47_check_paired

theorem treePart48_check_paired :
    treePart48.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart48_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart48_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart48_check_paired

theorem treePart49_check_paired :
    treePart49.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0]]) = true := by
  decide +kernel

theorem treePart49_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart49_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart49_check_paired

theorem treePart50_check_paired :
    treePart50.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart50_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart50_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart50_check_paired

theorem treePart51_check_paired :
    treePart51.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0,
      0, 0])]) = true := by
  decide +kernel

theorem treePart51_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart51_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart51_check_paired

theorem treePart52_check_paired :
    treePart52.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart52_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart52_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart52_check_paired

theorem treePart53_check_paired :
    treePart53.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart53_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart53_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart53_check_paired

theorem treePart54_check_paired :
    treePart54.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart54_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart54_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart54_check_paired

theorem treePart55_check_paired :
    treePart55.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart55_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart55_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart55_check_paired

theorem treePart56_check_paired :
    treePart56.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart56_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart56_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart56_check_paired

theorem treePart57_check_paired :
    treePart57.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart57_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart57_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart57_check_paired

theorem treePart58_check_paired :
    treePart58.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart58_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart58_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart58_check_paired

theorem treePart59_check_paired :
    treePart59.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart59_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart59_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart59_check_paired

end ReplayChecks6

end AtanasovRanganathan.GenusFiveRow03FixedCover
