/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverData
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverChecks0
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverChecks1
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverChecks2
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverChecks3
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverChecks4
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04FixedCoverChecks5

/-! **Independent generated check.** This module provides an additional generated proof of row 04
and is not imported by the main `LowGenus` root.

Generated exact replay of the fixed AR row-04 divisor on a
fundamental domain for the core's slot-level symmetry group.

The external discovery data are untrusted: `cells_check` and
`tree_check` replay every arithmetic obligation in the kernel, and the
chamber is discharged by the generated coverage theorem, so the
conclusion is the row on the whole closed orthant.

Passive definitions are re-exported from the data module. Bounded kernel-replay batches
limit cumulative checking cost; the wrappers retain the original auxiliary declarations. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04FixedCover

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow04CoverBase
open GenusFiveRow04Symmetry (Chamber chamber_covers)

theorem cells_check :
    cells.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [cells, List.all_append, GenusFiveRow04CoverCells0.chunk_check,
    GenusFiveRow04CoverCells1.chunk_check]

theorem cells_valid : ∀ cell ∈ cells, cell.certificate.ValidClosed 4 := by
  intro cell hCell
  have hChecks := (List.all_eq_true.mp cells_check) cell hCell
  exact (ExplicitPotential.CertificateData.checkClosed_eq_true_iff _ _).mp hChecks

theorem splitForm0 : splitForms.getD 0 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1] := by rfl

theorem splitForm1 : splitForms.getD 1 0 = aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm2 : splitForms.getD 2 0 = aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm3 : splitForms.getD 3 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1] := by rfl

theorem splitForm4 : splitForms.getD 4 0 = aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm5 : splitForms.getD 5 0 = aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm6 : splitForms.getD 6 0 = aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm7 : splitForms.getD 7 0 = aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm8 : splitForms.getD 8 0 = aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm9 : splitForms.getD 9 0 = aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm10 : splitForms.getD 10 0 = aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm11 : splitForms.getD 11 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0] := by rfl

theorem splitForm12 : splitForms.getD 12 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1] := by rfl

theorem splitForm13 : splitForms.getD 13 0 = aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1] := by rfl

theorem splitForm14 :
    splitForms.getD 14 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1] := by rfl

theorem splitForm15 :
    splitForms.getD 15 0 = aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm16 : splitForms.getD 16 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1] := by rfl

theorem splitForm17 :
    splitForms.getD 17 0 = aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm18 :
    splitForms.getD 18 0 = aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm19 : splitForms.getD 19 0 = aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm20 :
    splitForms.getD 20 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1] := by rfl

theorem splitForm21 :
    splitForms.getD 21 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1] := by rfl

theorem splitForm22 : splitForms.getD 22 0 = aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1] := by rfl

theorem splitForm23 : splitForms.getD 23 0 = aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm24 :
    splitForms.getD 24 0 = aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm25 :
    splitForms.getD 25 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1] := by rfl

theorem splitForm26 : splitForms.getD 26 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1] := by rfl

theorem splitForm27 : splitForms.getD 27 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1] := by rfl

theorem splitForm28 : splitForms.getD 28 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1] := by rfl

theorem splitForm29 :
    splitForms.getD 29 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1] := by rfl

theorem splitForm30 : splitForms.getD 30 0 = aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm31 : splitForms.getD 31 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1] := by rfl

private theorem treePart0_check_chunked :
    treePart0.checkLookup splitForms farkasReceiptLookup cells
      ((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart0_check_chunked

theorem treePart0_check :
    treePart0.check splitForms farkasReceipts cells
      ((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart0_check_chunked

private theorem treePart1_check_chunked :
    treePart1.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]])
      ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart1_check_chunked

theorem treePart1_check :
    treePart1.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]])
      ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart1_check_chunked

private theorem treePart2_check_chunked :
    treePart2.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart2_check_chunked

theorem treePart2_check :
    treePart2.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart2_check_chunked

private theorem treePart3_check_chunked :
    treePart3.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart3_check_chunked

theorem treePart3_check :
    treePart3.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart3_check_chunked

private theorem treePart4_check_chunked :
    treePart4.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart4_check_chunked

theorem treePart4_check :
    treePart4.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart4_check_chunked

private theorem treePart5_check_chunked :
    treePart5.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])])
      = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart5_check_chunked

theorem treePart5_check :
    treePart5.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])])
      = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart5_check_chunked

private theorem treePart6_check_chunked :
    treePart6.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, -1, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart6_check_chunked

theorem treePart6_check :
    treePart6.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, -1, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart6_check_chunked

private theorem treePart7_check_chunked :
    treePart7.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks0.treePart7_check_chunked

theorem treePart7_check :
    treePart7.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart7_check_chunked

private theorem treePart8_check_chunked :
    treePart8.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart8_check_chunked

theorem treePart8_check :
    treePart8.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart8_check_chunked

private theorem treePart9_check_chunked :
    treePart9.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart9_check_chunked

theorem treePart9_check :
    treePart9.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart9_check_chunked

private theorem treePart10_check_chunked :
    treePart10.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart10_check_chunked

theorem treePart10_check :
    treePart10.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart10_check_chunked

private theorem treePart11_check_chunked :
    treePart11.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart11_check_chunked

theorem treePart11_check :
    treePart11.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart11_check_chunked

private theorem treePart12_check_chunked :
    treePart12.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart12_check_chunked

theorem treePart12_check :
    treePart12.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart12_check_chunked

private theorem treePart13_check_chunked :
    treePart13.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart13_check_chunked

theorem treePart13_check :
    treePart13.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart13_check_chunked

private theorem treePart14_check_chunked :
    treePart14.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff
      [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart14_check_chunked

theorem treePart14_check :
    treePart14.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff
      [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart14_check_chunked

private theorem treePart15_check_chunked :
    treePart15.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart15_check_chunked

theorem treePart15_check :
    treePart15.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart15_check_chunked

private theorem treePart16_check_chunked :
    treePart16.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart16_check_chunked

theorem treePart16_check :
    treePart16.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart16_check_chunked

private theorem treePart17_check_chunked :
    treePart17.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart17_check_chunked

theorem treePart17_check :
    treePart17.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart17_check_chunked

private theorem treePart18_check_chunked :
    treePart18.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart18_check_chunked

theorem treePart18_check :
    treePart18.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart18_check_chunked

private theorem treePart19_check_chunked :
    treePart19.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])])
      = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart19_check_chunked

theorem treePart19_check :
    treePart19.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])])
      = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart19_check_chunked

private theorem treePart20_check_chunked :
    treePart20.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart20_check_chunked

theorem treePart20_check :
    treePart20.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart20_check_chunked

private theorem treePart21_check_chunked :
    treePart21.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart21_check_chunked

theorem treePart21_check :
    treePart21.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart21_check_chunked

private theorem treePart22_check_chunked :
    treePart22.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks0.treePart22_check_chunked

theorem treePart22_check :
    treePart22.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart22_check_chunked

private theorem treePart23_check_chunked :
    treePart23.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks0.treePart23_check_chunked

theorem treePart23_check :
    treePart23.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart23_check_chunked

private theorem treePart24_check_chunked :
    treePart24.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart24_check_chunked

theorem treePart24_check :
    treePart24.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart24_check_chunked

private theorem treePart25_check_chunked :
    treePart25.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks1.treePart25_check_chunked

theorem treePart25_check :
    treePart25.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart25_check_chunked

private theorem treePart26_check_chunked :
    treePart26.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart26_check_chunked

theorem treePart26_check :
    treePart26.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart26_check_chunked

private theorem treePart27_check_chunked :
    treePart27.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart27_check_chunked

theorem treePart27_check :
    treePart27.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart27_check_chunked

private theorem treePart28_check_chunked :
    treePart28.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart28_check_chunked

theorem treePart28_check :
    treePart28.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart28_check_chunked

private theorem treePart29_check_chunked :
    treePart29.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart29_check_chunked

theorem treePart29_check :
    treePart29.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart29_check_chunked

private theorem treePart30_check_chunked :
    treePart30.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart30_check_chunked

theorem treePart30_check :
    treePart30.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart30_check_chunked

private theorem treePart31_check_chunked :
    treePart31.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart31_check_chunked

theorem treePart31_check :
    treePart31.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart31_check_chunked

private theorem treePart32_check_chunked :
    treePart32.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1,
      -1, 0, 0, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart32_check_chunked

theorem treePart32_check :
    treePart32.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1,
      -1, 0, 0, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart32_check_chunked

private theorem treePart33_check_chunked :
    treePart33.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart33_check_chunked

theorem treePart33_check :
    treePart33.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart33_check_chunked

private theorem treePart34_check_chunked :
    treePart34.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart34_check_chunked

theorem treePart34_check :
    treePart34.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart34_check_chunked

private theorem treePart35_check_chunked :
    treePart35.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart35_check_chunked

theorem treePart35_check :
    treePart35.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart35_check_chunked

private theorem treePart36_check_chunked :
    treePart36.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, -1, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart36_check_chunked

theorem treePart36_check :
    treePart36.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, -1, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart36_check_chunked

private theorem treePart37_check_chunked :
    treePart37.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks1.treePart37_check_chunked

theorem treePart37_check :
    treePart37.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart37_check_chunked

private theorem treePart38_check_chunked :
    treePart38.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks1.treePart38_check_chunked

theorem treePart38_check :
    treePart38.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart38_check_chunked

private theorem treePart39_check_chunked :
    treePart39.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks1.treePart39_check_chunked

theorem treePart39_check :
    treePart39.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart39_check_chunked

private theorem treePart40_check_chunked :
    treePart40.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks1.treePart40_check_chunked

theorem treePart40_check :
    treePart40.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart40_check_chunked

private theorem treePart41_check_chunked :
    treePart41.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks1.treePart41_check_chunked

theorem treePart41_check :
    treePart41.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart41_check_chunked

private theorem treePart42_check_chunked :
    treePart42.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks1.treePart42_check_chunked

theorem treePart42_check :
    treePart42.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart42_check_chunked

private theorem treePart43_check_chunked :
    treePart43.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks1.treePart43_check_chunked

theorem treePart43_check :
    treePart43.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart43_check_chunked

private theorem treePart44_check_chunked :
    treePart44.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks1.treePart44_check_chunked

theorem treePart44_check :
    treePart44.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart44_check_chunked

private theorem treePart45_check_chunked :
    treePart45.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks1.treePart45_check_chunked

theorem treePart45_check :
    treePart45.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart45_check_chunked

private theorem treePart46_check_chunked :
    treePart46.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks1.treePart46_check_chunked

theorem treePart46_check :
    treePart46.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart46_check_chunked

private theorem treePart47_check_chunked :
    treePart47.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks1.treePart47_check_chunked

theorem treePart47_check :
    treePart47.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart47_check_chunked

private theorem treePart48_check_chunked :
    treePart48.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart48_check_chunked

theorem treePart48_check :
    treePart48.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart48_check_chunked

private theorem treePart49_check_chunked :
    treePart49.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart49_check_chunked

theorem treePart49_check :
    treePart49.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart49_check_chunked

private theorem treePart50_check_chunked :
    treePart50.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart50_check_chunked

theorem treePart50_check :
    treePart50.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart50_check_chunked

private theorem treePart51_check_chunked :
    treePart51.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart51_check_chunked

theorem treePart51_check :
    treePart51.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart51_check_chunked

private theorem treePart52_check_chunked :
    treePart52.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart52_check_chunked

theorem treePart52_check :
    treePart52.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart52_check_chunked

private theorem treePart53_check_chunked :
    treePart53.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart53_check_chunked

theorem treePart53_check :
    treePart53.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart53_check_chunked

private theorem treePart54_check_chunked :
    treePart54.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart54_check_chunked

theorem treePart54_check :
    treePart54.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart54_check_chunked

private theorem treePart55_check_chunked :
    treePart55.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart55_check_chunked

theorem treePart55_check :
    treePart55.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart55_check_chunked

private theorem treePart56_check_chunked :
    treePart56.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart56_check_chunked

theorem treePart56_check :
    treePart56.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart56_check_chunked

private theorem treePart57_check_chunked :
    treePart57.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart57_check_chunked

theorem treePart57_check :
    treePart57.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart57_check_chunked

private theorem treePart58_check_chunked :
    treePart58.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart58_check_chunked

theorem treePart58_check :
    treePart58.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart58_check_chunked

private theorem treePart59_check_chunked :
    treePart59.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart59_check_chunked

theorem treePart59_check :
    treePart59.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart59_check_chunked

private theorem treePart60_check_chunked :
    treePart60.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart60_check_chunked

theorem treePart60_check :
    treePart60.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart60_check_chunked

private theorem treePart61_check_chunked :
    treePart61.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks2.treePart61_check_chunked

theorem treePart61_check :
    treePart61.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart61_check_chunked

private theorem treePart62_check_chunked :
    treePart62.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart62_check_chunked

theorem treePart62_check :
    treePart62.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart62_check_chunked

private theorem treePart63_check_chunked :
    treePart63.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart63_check_chunked

theorem treePart63_check :
    treePart63.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart63_check_chunked

private theorem treePart64_check_chunked :
    treePart64.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart64_check_chunked

theorem treePart64_check :
    treePart64.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart64_check_chunked

private theorem treePart65_check_chunked :
    treePart65.checkLookup splitForms farkasReceiptLookup cells
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
  as_aux_lemma =>
    exact ReplayChecks2.treePart65_check_chunked

theorem treePart65_check :
    treePart65.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart65_check_chunked

private theorem treePart66_check_chunked :
    treePart66.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart66_check_chunked

theorem treePart66_check :
    treePart66.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart66_check_chunked

private theorem treePart67_check_chunked :
    treePart67.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart67_check_chunked

theorem treePart67_check :
    treePart67.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart67_check_chunked

private theorem treePart68_check_chunked :
    treePart68.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart68_check_chunked

theorem treePart68_check :
    treePart68.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart68_check_chunked

private theorem treePart69_check_chunked :
    treePart69.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart69_check_chunked

theorem treePart69_check :
    treePart69.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart69_check_chunked

private theorem treePart70_check_chunked :
    treePart70.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart70_check_chunked

theorem treePart70_check :
    treePart70.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart70_check_chunked

private theorem treePart71_check_chunked :
    treePart71.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks2.treePart71_check_chunked

theorem treePart71_check :
    treePart71.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart71_check_chunked

private theorem treePart72_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart72_check_chunked

theorem treePart72_check :
    treePart72.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart72_check_chunked

private theorem treePart73_check_chunked :
    treePart73.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart73_check_chunked

theorem treePart73_check :
    treePart73.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart73_check_chunked

private theorem treePart74_check_chunked :
    treePart74.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart74_check_chunked

theorem treePart74_check :
    treePart74.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart74_check_chunked

private theorem treePart75_check_chunked :
    treePart75.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart75_check_chunked

theorem treePart75_check :
    treePart75.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart75_check_chunked

private theorem treePart76_check_chunked :
    treePart76.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart76_check_chunked

theorem treePart76_check :
    treePart76.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart76_check_chunked

private theorem treePart77_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart77_check_chunked

theorem treePart77_check :
    treePart77.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart77_check_chunked

private theorem treePart78_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart78_check_chunked

theorem treePart78_check :
    treePart78.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1,
      0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart78_check_chunked

private theorem treePart79_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart79_check_chunked

theorem treePart79_check :
    treePart79.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff [0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart79_check_chunked

private theorem treePart80_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart80_check_chunked

theorem treePart80_check :
    treePart80.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff [0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart80_check_chunked

private theorem treePart81_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart81_check_chunked

theorem treePart81_check :
    treePart81.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart81_check_chunked

private theorem treePart82_check_chunked :
    treePart82.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart82_check_chunked

theorem treePart82_check :
    treePart82.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart82_check_chunked

private theorem treePart83_check_chunked :
    treePart83.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart83_check_chunked

theorem treePart83_check :
    treePart83.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart83_check_chunked

private theorem treePart84_check_chunked :
    treePart84.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart84_check_chunked

theorem treePart84_check :
    treePart84.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart84_check_chunked

private theorem treePart85_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart85_check_chunked

theorem treePart85_check :
    treePart85.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart85_check_chunked

private theorem treePart86_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart86_check_chunked

theorem treePart86_check :
    treePart86.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart86_check_chunked

private theorem treePart87_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart87_check_chunked

theorem treePart87_check :
    treePart87.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart87_check_chunked

private theorem treePart88_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart88_check_chunked

theorem treePart88_check :
    treePart88.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
      -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart88_check_chunked

private theorem treePart89_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart89_check_chunked

theorem treePart89_check :
    treePart89.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart89_check_chunked

private theorem treePart90_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart90_check_chunked

theorem treePart90_check :
    treePart90.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart90_check_chunked

private theorem treePart91_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart91_check_chunked

theorem treePart91_check :
    treePart91.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart91_check_chunked

private theorem treePart92_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart92_check_chunked

theorem treePart92_check :
    treePart92.check splitForms farkasReceipts cells
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
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart92_check_chunked

private theorem treePart93_check_chunked :
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
  as_aux_lemma =>
    exact ReplayChecks3.treePart93_check_chunked

theorem treePart93_check :
    treePart93.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart93_check_chunked

private theorem treePart94_check_chunked :
    treePart94.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart94_check_chunked

theorem treePart94_check :
    treePart94.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart94_check_chunked

private theorem treePart95_check_chunked :
    treePart95.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks3.treePart95_check_chunked

theorem treePart95_check :
    treePart95.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart95_check_chunked

private theorem treePart96_check_chunked :
    treePart96.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, -1, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart96_check_chunked

theorem treePart96_check :
    treePart96.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, -1, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart96_check_chunked

private theorem treePart97_check_chunked :
    treePart97.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart97_check_chunked

theorem treePart97_check :
    treePart97.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart97_check_chunked

private theorem treePart98_check_chunked :
    treePart98.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart98_check_chunked

theorem treePart98_check :
    treePart98.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart98_check_chunked

private theorem treePart99_check_chunked :
    treePart99.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart99_check_chunked

theorem treePart99_check :
    treePart99.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart99_check_chunked

private theorem treePart100_check_chunked :
    treePart100.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart100_check_chunked

theorem treePart100_check :
    treePart100.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart100_check_chunked

private theorem treePart101_check_chunked :
    treePart101.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart101_check_chunked

theorem treePart101_check :
    treePart101.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart101_check_chunked

private theorem treePart102_check_chunked :
    treePart102.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart102_check_chunked

theorem treePart102_check :
    treePart102.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart102_check_chunked

private theorem treePart103_check_chunked :
    treePart103.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart103_check_chunked

theorem treePart103_check :
    treePart103.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart103_check_chunked

private theorem treePart104_check_chunked :
    treePart104.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart104_check_chunked

theorem treePart104_check :
    treePart104.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart104_check_chunked

private theorem treePart105_check_chunked :
    treePart105.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart105_check_chunked

theorem treePart105_check :
    treePart105.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart105_check_chunked

private theorem treePart106_check_chunked :
    treePart106.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart106_check_chunked

theorem treePart106_check :
    treePart106.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart106_check_chunked

private theorem treePart107_check_chunked :
    treePart107.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart107_check_chunked

theorem treePart107_check :
    treePart107.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart107_check_chunked

private theorem treePart108_check_chunked :
    treePart108.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart108_check_chunked

theorem treePart108_check :
    treePart108.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart108_check_chunked

private theorem treePart109_check_chunked :
    treePart109.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart109_check_chunked

theorem treePart109_check :
    treePart109.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart109_check_chunked

private theorem treePart110_check_chunked :
    treePart110.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1,
      0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart110_check_chunked

theorem treePart110_check :
    treePart110.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1,
      0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart110_check_chunked

private theorem treePart111_check_chunked :
    treePart111.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1,
      0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])])
      = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart111_check_chunked

theorem treePart111_check :
    treePart111.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1,
      0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])])
      = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart111_check_chunked

private theorem treePart112_check_chunked :
    treePart112.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart112_check_chunked

theorem treePart112_check :
    treePart112.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart112_check_chunked

private theorem treePart113_check_chunked :
    treePart113.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks4.treePart113_check_chunked

theorem treePart113_check :
    treePart113.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart113_check_chunked

private theorem treePart114_check_chunked :
    treePart114.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart114_check_chunked

theorem treePart114_check :
    treePart114.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart114_check_chunked

private theorem treePart115_check_chunked :
    treePart115.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart115_check_chunked

theorem treePart115_check :
    treePart115.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart115_check_chunked

private theorem treePart116_check_chunked :
    treePart116.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart116_check_chunked

theorem treePart116_check :
    treePart116.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart116_check_chunked

private theorem treePart117_check_chunked :
    treePart117.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart117_check_chunked

theorem treePart117_check :
    treePart117.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart117_check_chunked

private theorem treePart118_check_chunked :
    treePart118.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart118_check_chunked

theorem treePart118_check :
    treePart118.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart118_check_chunked

private theorem treePart119_check_chunked :
    treePart119.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart119_check_chunked

theorem treePart119_check :
    treePart119.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart119_check_chunked

private theorem treePart120_check_chunked :
    treePart120.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks5.treePart120_check_chunked

theorem treePart120_check :
    treePart120.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart120_check_chunked

private theorem treePart121_check_chunked :
    treePart121.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart121_check_chunked

theorem treePart121_check :
    treePart121.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart121_check_chunked

private theorem treePart122_check_chunked :
    treePart122.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart122_check_chunked

theorem treePart122_check :
    treePart122.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart122_check_chunked

private theorem treePart123_check_chunked :
    treePart123.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart123_check_chunked

theorem treePart123_check :
    treePart123.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart123_check_chunked

private theorem treePart124_check_chunked :
    treePart124.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart124_check_chunked

theorem treePart124_check :
    treePart124.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart124_check_chunked

private theorem treePart125_check_chunked :
    treePart125.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart125_check_chunked

theorem treePart125_check :
    treePart125.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart125_check_chunked

private theorem treePart126_check_chunked :
    treePart126.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart126_check_chunked

theorem treePart126_check :
    treePart126.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart126_check_chunked

private theorem treePart127_check_chunked :
    treePart127.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks5.treePart127_check_chunked

theorem treePart127_check :
    treePart127.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart127_check_chunked

private theorem treePart128_check_chunked :
    treePart128.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart128_check_chunked

theorem treePart128_check :
    treePart128.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart128_check_chunked

private theorem treePart129_check_chunked :
    treePart129.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart129_check_chunked

theorem treePart129_check :
    treePart129.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart129_check_chunked

private theorem treePart130_check_chunked :
    treePart130.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart130_check_chunked

theorem treePart130_check :
    treePart130.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart130_check_chunked

private theorem treePart131_check_chunked :
    treePart131.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart131_check_chunked

theorem treePart131_check :
    treePart131.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart131_check_chunked

private theorem treePart132_check_chunked :
    treePart132.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0,
      0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart132_check_chunked

theorem treePart132_check :
    treePart132.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0,
      0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart132_check_chunked

private theorem treePart133_check_chunked :
    treePart133.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart133_check_chunked

theorem treePart133_check :
    treePart133.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart133_check_chunked

private theorem treePart134_check_chunked :
    treePart134.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart134_check_chunked

theorem treePart134_check :
    treePart134.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart134_check_chunked

private theorem treePart135_check_chunked :
    treePart135.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1,
      0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart135_check_chunked

theorem treePart135_check :
    treePart135.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1,
      0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart135_check_chunked

private theorem treePart136_check_chunked :
    treePart136.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart136_check_chunked

theorem treePart136_check :
    treePart136.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart136_check_chunked

private theorem treePart137_check_chunked :
    treePart137.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart137_check_chunked

theorem treePart137_check :
    treePart137.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart137_check_chunked

private theorem treePart138_check_chunked :
    treePart138.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart138_check_chunked

theorem treePart138_check :
    treePart138.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart138_check_chunked

private theorem treePart139_check_chunked :
    treePart139.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart139_check_chunked

theorem treePart139_check :
    treePart139.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart139_check_chunked

theorem treeAssemblyBranch0_check :
    treeAssemblyBranch0.check splitForms farkasReceipts cells
      (base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) = true := by
  simp only [treeAssemblyBranch0, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm2, splitForm3, splitForm4, splitForm5, splitForm6, splitForm7, splitForm8,
    splitForm9, splitForm10, treePart0_check, treePart1_check, treePart10_check,
    treePart11_check, treePart12_check, treePart13_check, treePart14_check, treePart15_check,
    treePart2_check, treePart3_check, treePart4_check, treePart5_check, treePart6_check,
    treePart7_check, treePart8_check, treePart9_check]

theorem treeAssemblyBranch1_check :
    treeAssemblyBranch1.check splitForms farkasReceipts cells
      ((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
        [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  simp only [treeAssemblyBranch1, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm3, splitForm8, splitForm9, splitForm11, splitForm12, splitForm13, splitForm14,
    splitForm15, splitForm16, treePart16_check, treePart17_check, treePart18_check,
    treePart19_check, treePart20_check, treePart21_check, treePart22_check, treePart23_check,
    treePart24_check, treePart25_check, treePart26_check, treePart27_check, treePart28_check,
    treePart29_check, treePart30_check, treePart31_check, treePart32_check, treePart33_check]

theorem treeAssemblyBranch2_check :
    treeAssemblyBranch2.check splitForms farkasReceipts cells
      (((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
        [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1,
        -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  simp only [treeAssemblyBranch2, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm3, splitForm5, splitForm6, splitForm7, splitForm8, splitForm9, splitForm10,
    splitForm11, splitForm12, splitForm13, splitForm14, splitForm16, splitForm17, splitForm18,
    splitForm19, splitForm20, splitForm21, splitForm22, splitForm23, splitForm24, splitForm25,
    splitForm26, splitForm27, splitForm28, splitForm29, treePart34_check, treePart35_check,
    treePart36_check, treePart37_check, treePart38_check, treePart39_check, treePart40_check,
    treePart41_check, treePart42_check, treePart43_check, treePart44_check, treePart45_check,
    treePart46_check, treePart47_check, treePart48_check, treePart49_check, treePart50_check,
    treePart51_check, treePart52_check, treePart53_check, treePart54_check, treePart55_check,
    treePart56_check, treePart57_check, treePart58_check, treePart59_check, treePart60_check,
    treePart61_check, treePart62_check, treePart63_check, treePart64_check, treePart65_check,
    treePart66_check, treePart67_check, treePart68_check, treePart69_check, treePart70_check,
    treePart71_check, treePart72_check, treePart73_check, treePart74_check, treePart75_check,
    treePart76_check, treePart77_check, treePart78_check, treePart79_check, treePart80_check,
    treePart81_check, treePart82_check, treePart83_check, treePart84_check, treePart85_check,
    treePart86_check, treePart87_check, treePart88_check, treePart89_check, treePart90_check,
    treePart91_check, treePart92_check, treePart93_check]

theorem treeAssemblyBranch3_check :
    treeAssemblyBranch3.check splitForms farkasReceipts cells
      (((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
        [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
        [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  simp only [treeAssemblyBranch3, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm3, splitForm6, splitForm7, splitForm8, splitForm9, splitForm10, splitForm11,
    splitForm12, splitForm13, splitForm14, splitForm15, splitForm16, splitForm19, splitForm23,
    splitForm24, treePart100_check, treePart101_check, treePart102_check, treePart103_check,
    treePart104_check, treePart105_check, treePart106_check, treePart107_check,
    treePart108_check, treePart109_check, treePart110_check, treePart111_check,
    treePart112_check, treePart113_check, treePart114_check, treePart115_check,
    treePart116_check, treePart117_check, treePart118_check, treePart119_check,
    treePart120_check, treePart121_check, treePart122_check, treePart123_check,
    treePart124_check, treePart125_check, treePart126_check, treePart127_check,
    treePart128_check, treePart129_check, treePart130_check, treePart131_check,
    treePart132_check, treePart133_check, treePart134_check, treePart135_check,
    treePart136_check, treePart137_check, treePart138_check, treePart139_check,
    treePart94_check, treePart95_check, treePart96_check, treePart97_check, treePart98_check,
    treePart99_check]

theorem treeAssemblyBranch4_check :
    treeAssemblyBranch4.check splitForms farkasReceipts cells
      ((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
        [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  simp only [treeAssemblyBranch4, CompactCellTree.check_split, Bool.and_true, splitForm4,
    treeAssemblyBranch2_check, treeAssemblyBranch3_check]

theorem treeAssemblyBranch5_check :
    treeAssemblyBranch5.check splitForms farkasReceipts cells
      (base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) = true :=
        by
  simp only [treeAssemblyBranch5, CompactCellTree.check_split, Bool.and_true, splitForm2,
    treeAssemblyBranch1_check, treeAssemblyBranch4_check]

theorem tree_check :
    tree.check splitForms farkasReceipts cells base = true := by
  simp only [tree, CompactCellTree.check_split, Bool.and_true, splitForm0,
    treeAssemblyBranch0_check, treeAssemblyBranch5_check]

/-- On the chamber the eighteen active rows all hold: the first twelve
because lengths are natural numbers, the last six by definition of the
fundamental domain. -/
theorem base_holds (length : Fin 12 → ℕ) (hChamber : Chamber length) :
    ExplicitPotential.FormsHold base (lengthPoint length) := by
  obtain ⟨⟨q0, q1, q2, q3⟩, r0, r1⟩ := hChamber
  intro form hForm
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hForm
  rcases hForm with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals simp [aff,
    _root_.Utilities.Certificate.AffineCover.AffineForm.Holds,
    _root_.Utilities.Certificate.AffineCover.AffineForm.eval,
    lengthPoint, Fin.sum_univ_succ]
  all_goals omega

/-- Connectivity of the core, checked here so that the generated
modules stay self-contained. -/
theorem rowConnected : row04Core.Connected :=
  (row04Core.connectedCheck_eq_true_iff).mp (by decide +kernel)

theorem closedConstruction :
    ClosedSubdivisionDharConstruction row04Core (by norm_num) :=
  ClosedOrbit.closedConstruction_of_chamber row04Core (by norm_num) Chamber
    (fun length _ _ => chamber_covers length)
    (fun length forest notLoopy hChamber =>
      chamberPencil_of_compactCellTree (by norm_num) rowConnected
        cells base splitForms farkasReceipts tree cells_valid tree_check
        length forest notLoopy (base_holds length hChamber))

end AtanasovRanganathan.GenusFiveRow04FixedCover
