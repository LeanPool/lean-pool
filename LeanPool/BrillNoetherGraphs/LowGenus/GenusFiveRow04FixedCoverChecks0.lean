/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.PairedCoverReplay

/-! # Kernel replay batch 0 for the independent row-04 cover

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

namespace ReplayChecks0

attribute [local instance 2000] CompactCellTree.decidableCheckPaired

theorem treePart0_check_paired :
    treePart0.checkPaired splitForms farkasReceiptLookup cells
      ((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart0_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart0_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart0_check_paired

theorem treePart1_check_paired :
    treePart1.checkPaired splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]])
      ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart1_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart1_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart1_check_paired

theorem treePart2_check_paired :
    treePart2.checkPaired splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) = true := by
  decide +kernel

theorem treePart2_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart2_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart2_check_paired

theorem treePart3_check_paired :
    treePart3.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

theorem treePart3_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart3_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart3_check_paired

theorem treePart4_check_paired :
    treePart4.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart4_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart4_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart4_check_paired

theorem treePart5_check_paired :
    treePart5.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])])
      = true := by
  decide +kernel

theorem treePart5_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart5_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart5_check_paired

theorem treePart6_check_paired :
    treePart6.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, -1, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart6_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart6_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart6_check_paired

theorem treePart7_check_paired :
    treePart7.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true
  := by
  decide +kernel

theorem treePart7_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart7_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart7_check_paired

theorem treePart8_check_paired :
    treePart8.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) = true := by
  decide +kernel

theorem treePart8_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart8_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart8_check_paired

theorem treePart9_check_paired :
    treePart9.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart9_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart9_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart9_check_paired

theorem treePart10_check_paired :
    treePart10.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart10_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart10_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart10_check_paired

theorem treePart11_check_paired :
    treePart11.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart11_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart11_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart11_check_paired

theorem treePart12_check_paired :
    treePart12.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart12_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart12_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart12_check_paired

theorem treePart13_check_paired :
    treePart13.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart13_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart13_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart13_check_paired

theorem treePart14_check_paired :
    treePart14.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff
      [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart14_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart14_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart14_check_paired

theorem treePart15_check_paired :
    treePart15.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart15_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart15_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart15_check_paired

theorem treePart16_check_paired :
    treePart16.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart16_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart16_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart16_check_paired

theorem treePart17_check_paired :
    treePart17.checkPaired splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) =
      true := by
  decide +kernel

theorem treePart17_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart17_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart17_check_paired

theorem treePart18_check_paired :
    treePart18.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart18_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart18_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart18_check_paired

theorem treePart19_check_paired :
    treePart19.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])])
      = true := by
  decide +kernel

theorem treePart19_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart19_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart19_check_paired

theorem treePart20_check_paired :
    treePart20.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  decide +kernel

theorem treePart20_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart20_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart20_check_paired

theorem treePart21_check_paired :
    treePart21.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) = true := by
  decide +kernel

theorem treePart21_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart21_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart21_check_paired

theorem treePart22_check_paired :
    treePart22.checkPaired splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart22_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart22_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart22_check_paired

theorem treePart23_check_paired :
    treePart23.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true
  := by
  decide +kernel

theorem treePart23_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart23_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart23_check_paired

end ReplayChecks0

end AtanasovRanganathan.GenusFiveRow04FixedCover
