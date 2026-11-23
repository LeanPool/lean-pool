/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.PairedCoverReplay

/-! # Kernel replay batch 1 for the independent row-04 cover

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

namespace ReplayChecks1

attribute [local instance 2000] CompactCellTree.decidableCheckPaired

theorem treePart24_check_paired :
    treePart24.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  decide +kernel

theorem treePart24_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart24_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart24_check_paired

theorem treePart25_check_paired :
    treePart25.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true
  := by
  decide +kernel

theorem treePart25_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart25_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart25_check_paired

theorem treePart26_check_paired :
    treePart26.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  decide +kernel

theorem treePart26_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart26_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart26_check_paired

theorem treePart27_check_paired :
    treePart27.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  decide +kernel

theorem treePart27_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart27_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart27_check_paired

theorem treePart28_check_paired :
    treePart28.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  decide +kernel

theorem treePart28_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart28_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart28_check_paired

theorem treePart29_check_paired :
    treePart29.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart29_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart29_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart29_check_paired

theorem treePart30_check_paired :
    treePart30.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart30_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart30_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart30_check_paired

theorem treePart31_check_paired :
    treePart31.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) =
      true := by
  decide +kernel

theorem treePart31_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart31_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart31_check_paired

theorem treePart32_check_paired :
    treePart32.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1,
      -1, 0, 0, 1, 0, 1])]) = true := by
  decide +kernel

theorem treePart32_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart32_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart32_check_paired

theorem treePart33_check_paired :
    treePart33.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  decide +kernel

theorem treePart33_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart33_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart33_check_paired

theorem treePart34_check_paired :
    treePart34.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart34_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart34_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart34_check_paired

theorem treePart35_check_paired :
    treePart35.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart35_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart35_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart35_check_paired

theorem treePart36_check_paired :
    treePart36.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, -1, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart36_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart36_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart36_check_paired

theorem treePart37_check_paired :
    treePart37.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true
  := by
  decide +kernel

theorem treePart37_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart37_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart37_check_paired

theorem treePart38_check_paired :
    treePart38.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart38_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart38_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart38_check_paired

theorem treePart39_check_paired :
    treePart39.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0,
      0, 1]]) = true := by
  decide +kernel

theorem treePart39_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart39_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart39_check_paired

theorem treePart40_check_paired :
    treePart40.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true
  := by
  decide +kernel

theorem treePart40_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart40_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart40_check_paired

theorem treePart41_check_paired :
    treePart41.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart41_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart41_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart41_check_paired

theorem treePart42_check_paired :
    treePart42.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1,
      -1]]) = true := by
  decide +kernel

theorem treePart42_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart42_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart42_check_paired

theorem treePart43_check_paired :
    treePart43.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1]]) = true := by
  decide +kernel

theorem treePart43_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart43_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart43_check_paired

theorem treePart44_check_paired :
    treePart44.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart44_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart44_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart44_check_paired

theorem treePart45_check_paired :
    treePart45.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1]]) = true := by
  decide +kernel

theorem treePart45_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart45_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart45_check_paired

theorem treePart46_check_paired :
    treePart46.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      -1, -1, 0, -1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart46_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart46_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart46_check_paired

theorem treePart47_check_paired :
    treePart47.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      -1, -1, 0, -1, 1, 0, 1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0,
      -1])]) = true := by
  decide +kernel

theorem treePart47_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart47_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart47_check_paired

end ReplayChecks1

end AtanasovRanganathan.GenusFiveRow04FixedCover
