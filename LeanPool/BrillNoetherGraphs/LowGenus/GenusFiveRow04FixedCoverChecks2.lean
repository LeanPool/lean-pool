/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverData
public import LeanPool.BrillNoetherGraphs.LowGenus.PairedCoverReplay

/-! # Kernel replay batch 2 for the independent row-04 cover

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

namespace ReplayChecks2

attribute [local instance 2000] CompactCellTree.decidableCheckPaired

theorem treePart48_check_paired :
    treePart48.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
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
      -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  decide +kernel

theorem treePart48_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart48_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart48_check_paired

theorem treePart49_check_paired :
    treePart49.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart49_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart49_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart49_check_paired

theorem treePart50_check_paired :
    treePart50.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart50_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart50_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart50_check_paired

theorem treePart51_check_paired :
    treePart51.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart51_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart51_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart51_check_paired

theorem treePart52_check_paired :
    treePart52.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart52_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart52_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart52_check_paired

theorem treePart53_check_paired :
    treePart53.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0,
      -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart53_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart53_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart53_check_paired

theorem treePart54_check_paired :
    treePart54.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff
      [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  decide +kernel

theorem treePart54_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart54_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart54_check_paired

theorem treePart55_check_paired :
    treePart55.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])]) = true := by
  decide +kernel

theorem treePart55_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart55_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart55_check_paired

theorem treePart56_check_paired :
    treePart56.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0,
      0, 0, 1])]) = true := by
  decide +kernel

theorem treePart56_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart56_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart56_check_paired

theorem treePart57_check_paired :
    treePart57.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart57_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart57_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart57_check_paired

theorem treePart58_check_paired :
    treePart58.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart58_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart58_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart58_check_paired

theorem treePart59_check_paired :
    treePart59.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart59_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart59_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart59_check_paired

theorem treePart60_check_paired :
    treePart60.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart60_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart60_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart60_check_paired

theorem treePart61_check_paired :
    treePart61.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true
  := by
  decide +kernel

theorem treePart61_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart61_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart61_check_paired

theorem treePart62_check_paired :
    treePart62.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart62_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart62_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart62_check_paired

theorem treePart63_check_paired :
    treePart63.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart63_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart63_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart63_check_paired

theorem treePart64_check_paired :
    treePart64.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

theorem treePart64_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart64_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart64_check_paired

theorem treePart65_check_paired :
    treePart65.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

theorem treePart65_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart65_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart65_check_paired

theorem treePart66_check_paired :
    treePart66.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

theorem treePart66_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart66_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart66_check_paired

theorem treePart67_check_paired :
    treePart67.checkPaired splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

theorem treePart67_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart67_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart67_check_paired

theorem treePart68_check_paired :
    treePart68.checkPaired splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart68_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart68_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart68_check_paired

theorem treePart69_check_paired :
    treePart69.checkPaired splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) = true := by
  decide +kernel

theorem treePart69_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart69_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart69_check_paired

theorem treePart70_check_paired :
    treePart70.checkPaired splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

theorem treePart70_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart70_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart70_check_paired

theorem treePart71_check_paired :
    treePart71.checkPaired splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

theorem treePart71_check_chunked :
    type_of% (CompactCellTree.checkLookup_of_checkPaired treePart71_check_paired) := by
  as_aux_lemma =>
    exact CompactCellTree.checkLookup_of_checkPaired treePart71_check_paired

end ReplayChecks2

end AtanasovRanganathan.GenusFiveRow04FixedCover
