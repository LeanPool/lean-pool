/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.PairedCoverReplay
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

attribute [local instance 2000] CompactCellTree.decidableCheckPaired

theorem treePart84_check_paired :
    treePart84.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart84_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart84_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart84_check_paired

theorem treePart85_check_paired :
    treePart85.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart85_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart85_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart85_check_paired

theorem treePart86_check_paired :
    treePart86.checkPaired splitForms farkasReceiptLookup cells
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

theorem treePart86_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart86_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart86_check_paired

theorem treePart87_check_paired :
    treePart87.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart87_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart87_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart87_check_paired

theorem treePart88_check_paired :
    treePart88.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart88_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart88_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart88_check_paired

theorem treePart89_check_paired :
    treePart89.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart89_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart89_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart89_check_paired

theorem treePart90_check_paired :
    treePart90.checkPaired splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1,
      0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart90_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart90_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart90_check_paired

theorem treePart91_check_paired :
    treePart91.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart91_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart91_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart91_check_paired

theorem treePart92_check_paired :
    treePart92.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart92_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart92_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart92_check_paired

theorem treePart93_check_paired :
    treePart93.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart93_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart93_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart93_check_paired

theorem treePart94_check_paired :
    treePart94.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++
      [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart94_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart94_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart94_check_paired

theorem treePart95_check_paired :
    treePart95.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart95_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart95_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart95_check_paired

theorem treePart96_check_paired :
    treePart96.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1,
      0, 1, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart96_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart96_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart96_check_paired

theorem treePart97_check_paired :
    treePart97.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true
      := by
  decide +kernel

theorem treePart97_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart97_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart97_check_paired

theorem treePart98_check_paired :
    treePart98.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart98_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart98_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart98_check_paired

theorem treePart99_check_paired :
    treePart99.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) =
      true := by
  decide +kernel

theorem treePart99_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart99_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart99_check_paired

theorem treePart100_check_paired :
    treePart100.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

theorem treePart100_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart100_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart100_check_paired

theorem treePart101_check_paired :
    treePart101.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

theorem treePart101_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart101_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart101_check_paired

theorem treePart102_check_paired :
    treePart102.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, -1]]) = true := by
  decide +kernel

theorem treePart102_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart102_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart102_check_paired

theorem treePart103_check_paired :
    treePart103.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) = true
  := by
  decide +kernel

theorem treePart103_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart103_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart103_check_paired

theorem treePart104_check_paired :
    treePart104.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
      0, 0, 0])]) = true := by
  decide +kernel

theorem treePart104_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart104_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart104_check_paired

theorem treePart105_check_paired :
    treePart105.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true
  := by
  decide +kernel

theorem treePart105_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart105_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart105_check_paired

theorem treePart106_check_paired :
    treePart106.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0, 0, 0])]) = true := by
  decide +kernel

theorem treePart106_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart106_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart106_check_paired

theorem treePart107_check_paired :
    treePart107.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart107_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart107_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart107_check_paired

end ReplayChecks8

end AtanasovRanganathan.GenusFiveRow03FixedCover
