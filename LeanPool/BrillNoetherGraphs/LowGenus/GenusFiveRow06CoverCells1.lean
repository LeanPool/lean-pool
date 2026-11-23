/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverBase
import LeanPool.BrillNoetherGraphs.LowGenus.IndexedCellReplay

/-! **Independent generated check.** This module provides an additional generated proof of row 06
and is not imported by the main `LowGenus` root.

Generated cell chunk 1 of 5 for the AR row-06 chamber cover
(cells 97-193).  Split across modules because the kernel cost of
replaying a cell is cumulative within one Lean process. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06CoverCells1

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow06CoverBase

/-- Closed-cover cell 97 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 18, 5, 12]`; `cell97_check` verifies its
explicit-potential certificate. -/
def cell97 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 18, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

attribute [local instance 2000] CertificateData.decidableCheckClosedRowsAtHints

private theorem cell97_check_hints : cell97.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0, 0, 18,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell97_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell97_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell97_check_hints

theorem cell97_check :
    cell97.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 18, 5, 12] witnessGeometryChecked (by decide))
      cell97_check_indexed

/-- Closed-cover cell 98 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 18, 5, 12]`; `cell98_check` verifies its
explicit-potential certificate. -/
def cell98 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 18, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell98_check_hints : cell98.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     22]] = true := by
  decide +kernel

private theorem cell98_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell98_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell98_check_hints

theorem cell98_check :
    cell98.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 18, 5, 12] witnessGeometryChecked (by decide))
      cell98_check_indexed

/-- Closed-cover cell 99 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 18, 5, 12]`; `cell99_check` verifies
its explicit-potential certificate. -/
def cell99 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 18, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell99_check_hints : cell99.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     22]] = true := by
  decide +kernel

private theorem cell99_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell99_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell99_check_hints

theorem cell99_check :
    cell99.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 18, 5, 12] witnessGeometryChecked (by decide))
      cell99_check_indexed

/-- Closed-cover cell 100 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 18, 5, 12]`; `cell100_check` verifies
its explicit-potential certificate. -/
def cell100 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 18, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell100_check_hints : cell100.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell100_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell100_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell100_check_hints

theorem cell100_check :
    cell100.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 18, 5, 12] witnessGeometryChecked (by decide))
      cell100_check_indexed

/-- Closed-cover cell 101 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 18, 5, 13]`; `cell101_check` verifies
its explicit-potential certificate. -/
def cell101 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 18, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell101_check_hints : cell101.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 0, 0, 6, 23]]
     = true := by
  decide +kernel

private theorem cell101_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell101_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell101_check_hints

theorem cell101_check :
    cell101.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 3, 18, 5, 13] witnessGeometryChecked (by decide))
      cell101_check_indexed

/-- Closed-cover cell 102 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 18, 5, 13]`; `cell102_check` verifies
its explicit-potential certificate. -/
def cell102 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 18, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell102_check_hints : cell102.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0, 0, 18,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell102_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell102_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell102_check_hints

theorem cell102_check :
    cell102.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 18, 5, 13] witnessGeometryChecked (by decide))
      cell102_check_indexed

/-- Closed-cover cell 103 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 18, 5, 13]`; `cell103_check` verifies
its explicit-potential certificate. -/
def cell103 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 18, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell103_check_hints : cell103.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell103_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell103_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell103_check_hints

theorem cell103_check :
    cell103.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 18, 5, 13] witnessGeometryChecked (by decide))
      cell103_check_indexed

/-- Closed-cover cell 104 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 18, 5, 13]`; `cell104_check` verifies
its explicit-potential certificate. -/
def cell104 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 18, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell104_check_hints : cell104.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell104_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell104_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell104_check_hints

theorem cell104_check :
    cell104.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 18, 5, 13] witnessGeometryChecked (by decide))
      cell104_check_indexed

/-- Closed-cover cell 105 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 18, 5, 13]`; `cell105_check` verifies
its explicit-potential certificate. -/
def cell105 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 18, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell105_check_hints : cell105.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell105_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell105_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell105_check_hints

theorem cell105_check :
    cell105.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 18, 5, 13] witnessGeometryChecked (by decide))
      cell105_check_indexed

/-- Closed-cover cell 106 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 18, 5, 14]`; `cell106_check` verifies
its explicit-potential certificate. -/
def cell106 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 18, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell106_check_hints : cell106.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 0, 0, 6, 23]]
     = true := by
  decide +kernel

private theorem cell106_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell106_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell106_check_hints

theorem cell106_check :
    cell106.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 3, 18, 5, 14] witnessGeometryChecked (by decide))
      cell106_check_indexed

/-- Closed-cover cell 107 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 18, 5, 14]`; `cell107_check` verifies
its explicit-potential certificate. -/
def cell107 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 18, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell107_check_hints : cell107.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0, 0, 18,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell107_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell107_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell107_check_hints

theorem cell107_check :
    cell107.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 18, 5, 14] witnessGeometryChecked (by decide))
      cell107_check_indexed

/-- Closed-cover cell 108 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 18, 5, 14]`; `cell108_check` verifies
its explicit-potential certificate. -/
def cell108 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 18, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell108_check_hints : cell108.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell108_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell108_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell108_check_hints

theorem cell108_check :
    cell108.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 18, 5, 14] witnessGeometryChecked (by decide))
      cell108_check_indexed

/-- Closed-cover cell 109 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 18, 5, 14]`; `cell109_check` verifies
its explicit-potential certificate. -/
def cell109 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 18, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell109_check_hints : cell109.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell109_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell109_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell109_check_hints

theorem cell109_check :
    cell109.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 18, 5, 14] witnessGeometryChecked (by decide))
      cell109_check_indexed

/-- Closed-cover cell 110 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 18, 5, 14]`; `cell110_check` verifies
its explicit-potential certificate. -/
def cell110 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 18, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell110_check_hints : cell110.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell110_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell110_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell110_check_hints

theorem cell110_check :
    cell110.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 18, 5, 14] witnessGeometryChecked (by decide))
      cell110_check_indexed

/-- Closed-cover cell 111 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 18, 5, 16]`; `cell111_check` verifies
its explicit-potential certificate. -/
def cell111 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 18, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell111_check_hints : cell111.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 21, 23]]
     = true := by
  decide +kernel

private theorem cell111_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell111_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell111_check_hints

theorem cell111_check :
    cell111.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 3, 18, 5, 16] witnessGeometryChecked (by decide))
      cell111_check_indexed

/-- Closed-cover cell 112 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 18, 5, 16]`; `cell112_check` verifies
its explicit-potential certificate. -/
def cell112 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 18, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell112_check_hints : cell112.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0, 0, 18,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell112_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell112_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell112_check_hints

theorem cell112_check :
    cell112.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 18, 5, 16] witnessGeometryChecked (by decide))
      cell112_check_indexed

/-- Closed-cover cell 113 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 18, 5, 16]`; `cell113_check` verifies
its explicit-potential certificate. -/
def cell113 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 18, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell113_check_hints : cell113.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22,
     24]] = true := by
  decide +kernel

private theorem cell113_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell113_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell113_check_hints

theorem cell113_check :
    cell113.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 18, 5, 16] witnessGeometryChecked (by decide))
      cell113_check_indexed

/-- Closed-cover cell 114 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 18, 5, 16]`; `cell114_check` verifies
its explicit-potential certificate. -/
def cell114 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 18, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell114_check_hints : cell114.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22,
     24]] = true := by
  decide +kernel

private theorem cell114_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell114_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell114_check_hints

theorem cell114_check :
    cell114.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 18, 5, 16] witnessGeometryChecked (by decide))
      cell114_check_indexed

/-- Closed-cover cell 115 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 18, 5, 16]`; `cell115_check` verifies
its explicit-potential certificate. -/
def cell115 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 18, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell115_check_hints : cell115.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22, 24]]
     = true := by
  decide +kernel

private theorem cell115_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell115_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell115_check_hints

theorem cell115_check :
    cell115.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 18, 5, 16] witnessGeometryChecked (by decide))
      cell115_check_indexed

/-- Closed-cover cell 116 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 19, 5, 12]`; `cell116_check` verifies
its explicit-potential certificate. -/
def cell116 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 19, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell116_check_hints : cell116.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21]]
     = true := by
  decide +kernel

private theorem cell116_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell116_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell116_check_hints

theorem cell116_check :
    cell116.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 3, 19, 5, 12] witnessGeometryChecked (by decide))
      cell116_check_indexed

/-- Closed-cover cell 117 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 19, 5, 12]`; `cell117_check` verifies
its explicit-potential certificate. -/
def cell117 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 19, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell117_check_hints : cell117.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0, 0, 18,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell117_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell117_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell117_check_hints

theorem cell117_check :
    cell117.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 19, 5, 12] witnessGeometryChecked (by decide))
      cell117_check_indexed

/-- Closed-cover cell 118 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 19, 5, 12]`; `cell118_check` verifies
its explicit-potential certificate. -/
def cell118 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 19, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell118_check_hints : cell118.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     22]] = true := by
  decide +kernel

private theorem cell118_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell118_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell118_check_hints

theorem cell118_check :
    cell118.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 19, 5, 12] witnessGeometryChecked (by decide))
      cell118_check_indexed

/-- Closed-cover cell 119 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 19, 5, 12]`; `cell119_check` verifies
its explicit-potential certificate. -/
def cell119 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 19, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell119_check_hints : cell119.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     22]] = true := by
  decide +kernel

private theorem cell119_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell119_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell119_check_hints

theorem cell119_check :
    cell119.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 19, 5, 12] witnessGeometryChecked (by decide))
      cell119_check_indexed

/-- Closed-cover cell 120 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 19, 5, 12]`; `cell120_check` verifies
its explicit-potential certificate. -/
def cell120 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 19, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell120_check_hints : cell120.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell120_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell120_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell120_check_hints

theorem cell120_check :
    cell120.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 19, 5, 12] witnessGeometryChecked (by decide))
      cell120_check_indexed

/-- Closed-cover cell 121 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 19, 5, 13]`; `cell121_check` verifies
its explicit-potential certificate. -/
def cell121 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 19, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell121_check_hints : cell121.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0, 0, 18,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell121_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell121_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell121_check_hints

theorem cell121_check :
    cell121.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 19, 5, 13] witnessGeometryChecked (by decide))
      cell121_check_indexed

/-- Closed-cover cell 122 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 19, 5, 14]`; `cell122_check` verifies
its explicit-potential certificate. -/
def cell122 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 19, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell122_check_hints : cell122.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0, 0, 18,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell122_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell122_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell122_check_hints

theorem cell122_check :
    cell122.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 19, 5, 14] witnessGeometryChecked (by decide))
      cell122_check_indexed

/-- Closed-cover cell 123 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 19, 5, 16]`; `cell123_check` verifies
its explicit-potential certificate. -/
def cell123 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 19, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell123_check_hints : cell123.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0, 0, 18,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell123_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell123_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell123_check_hints

theorem cell123_check :
    cell123.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 19, 5, 16] witnessGeometryChecked (by decide))
      cell123_check_indexed

/-- Closed-cover cell 124 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 19, 5, 13]`; `cell124_check` verifies
its explicit-potential certificate. -/
def cell124 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 19, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell124_check_hints : cell124.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell124_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell124_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell124_check_hints

theorem cell124_check :
    cell124.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 19, 5, 13] witnessGeometryChecked (by decide))
      cell124_check_indexed

/-- Closed-cover cell 125 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 19, 5, 14]`; `cell125_check` verifies
its explicit-potential certificate. -/
def cell125 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 19, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell125_check_hints : cell125.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell125_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell125_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell125_check_hints

theorem cell125_check :
    cell125.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 19, 5, 14] witnessGeometryChecked (by decide))
      cell125_check_indexed

/-- Closed-cover cell 126 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 19, 5, 16]`; `cell126_check` verifies
its explicit-potential certificate. -/
def cell126 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 19, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell126_check_hints : cell126.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22,
     24]] = true := by
  decide +kernel

private theorem cell126_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell126_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell126_check_hints

theorem cell126_check :
    cell126.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 19, 5, 16] witnessGeometryChecked (by decide))
      cell126_check_indexed

/-- Closed-cover cell 127 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 19, 5, 13]`; `cell127_check` verifies
its explicit-potential certificate. -/
def cell127 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 19, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell127_check_hints : cell127.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell127_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell127_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell127_check_hints

theorem cell127_check :
    cell127.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 19, 5, 13] witnessGeometryChecked (by decide))
      cell127_check_indexed

/-- Closed-cover cell 128 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 19, 5, 14]`; `cell128_check` verifies
its explicit-potential certificate. -/
def cell128 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 19, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell128_check_hints : cell128.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell128_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell128_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell128_check_hints

theorem cell128_check :
    cell128.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 19, 5, 14] witnessGeometryChecked (by decide))
      cell128_check_indexed

/-- Closed-cover cell 129 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 19, 5, 16]`; `cell129_check` verifies
its explicit-potential certificate. -/
def cell129 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 19, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell129_check_hints : cell129.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0,
     0, 0, 20, 11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22,
     24]] = true := by
  decide +kernel

private theorem cell129_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell129_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell129_check_hints

theorem cell129_check :
    cell129.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 19, 5, 16] witnessGeometryChecked (by decide))
      cell129_check_indexed

/-- Closed-cover cell 130 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 19, 5, 13]`; `cell130_check` verifies
its explicit-potential certificate. -/
def cell130 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 19, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell130_check_hints : cell130.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell130_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell130_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell130_check_hints

theorem cell130_check :
    cell130.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 19, 5, 13] witnessGeometryChecked (by decide))
      cell130_check_indexed

/-- Closed-cover cell 131 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 19, 5, 14]`; `cell131_check` verifies
its explicit-potential certificate. -/
def cell131 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 19, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell131_check_hints : cell131.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell131_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell131_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell131_check_hints

theorem cell131_check :
    cell131.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 19, 5, 14] witnessGeometryChecked (by decide))
      cell131_check_indexed

/-- Closed-cover cell 132 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 19, 5, 16]`; `cell132_check` verifies
its explicit-potential certificate. -/
def cell132 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 19, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell132_check_hints : cell132.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20,
     11], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22, 24]]
     = true := by
  decide +kernel

private theorem cell132_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell132_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell132_check_hints

theorem cell132_check :
    cell132.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 19, 5, 16] witnessGeometryChecked (by decide))
      cell132_check_indexed

/-- Closed-cover cell 133 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 21, 5, 12]`; `cell133_check` verifies
its explicit-potential certificate. -/
def cell133 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 21, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell133_check_hints : cell133.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21]]
     = true := by
  decide +kernel

private theorem cell133_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell133_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell133_check_hints

theorem cell133_check :
    cell133.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 3, 21, 5, 12] witnessGeometryChecked (by decide))
      cell133_check_indexed

/-- Closed-cover cell 134 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 21, 5, 12]`; `cell134_check` verifies
its explicit-potential certificate. -/
def cell134 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 21, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell134_check_hints : cell134.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 18,
     17], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell134_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell134_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell134_check_hints

theorem cell134_check :
    cell134.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 21, 5, 12] witnessGeometryChecked (by decide))
      cell134_check_indexed

/-- Closed-cover cell 135 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 21, 5, 12]`; `cell135_check` verifies
its explicit-potential certificate. -/
def cell135 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 21, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell135_check_hints : cell135.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     5, 22]] = true := by
  decide +kernel

private theorem cell135_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell135_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell135_check_hints

theorem cell135_check :
    cell135.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 21, 5, 12] witnessGeometryChecked (by decide))
      cell135_check_indexed

/-- Closed-cover cell 136 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 21, 5, 12]`; `cell136_check` verifies
its explicit-potential certificate. -/
def cell136 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 21, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell136_check_hints : cell136.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     5, 22]] = true := by
  decide +kernel

private theorem cell136_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell136_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell136_check_hints

theorem cell136_check :
    cell136.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 21, 5, 12] witnessGeometryChecked (by decide))
      cell136_check_indexed

/-- Closed-cover cell 137 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 21, 5, 12]`; `cell137_check` verifies
its explicit-potential certificate. -/
def cell137 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 21, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell137_check_hints : cell137.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell137_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell137_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell137_check_hints

theorem cell137_check :
    cell137.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 21, 5, 12] witnessGeometryChecked (by decide))
      cell137_check_indexed

/-- Closed-cover cell 138 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 21, 5, 13]`; `cell138_check` verifies
its explicit-potential certificate. -/
def cell138 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 21, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell138_check_hints : cell138.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 18,
     17], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell138_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell138_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell138_check_hints

theorem cell138_check :
    cell138.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 21, 5, 13] witnessGeometryChecked (by decide))
      cell138_check_indexed

/-- Closed-cover cell 139 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 21, 5, 14]`; `cell139_check` verifies
its explicit-potential certificate. -/
def cell139 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 21, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell139_check_hints : cell139.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 18,
     17], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell139_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell139_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell139_check_hints

theorem cell139_check :
    cell139.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 21, 5, 14] witnessGeometryChecked (by decide))
      cell139_check_indexed

/-- Closed-cover cell 140 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 21, 5, 16]`; `cell140_check` verifies
its explicit-potential certificate. -/
def cell140 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 21, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell140_check_hints : cell140.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 18,
     17], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell140_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell140_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell140_check_hints

theorem cell140_check :
    cell140.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 21, 5, 16] witnessGeometryChecked (by decide))
      cell140_check_indexed

/-- Closed-cover cell 141 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 21, 5, 13]`; `cell141_check` verifies
its explicit-potential certificate. -/
def cell141 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 21, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell141_check_hints : cell141.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell141_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell141_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell141_check_hints

theorem cell141_check :
    cell141.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 21, 5, 13] witnessGeometryChecked (by decide))
      cell141_check_indexed

/-- Closed-cover cell 142 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 21, 5, 14]`; `cell142_check` verifies
its explicit-potential certificate. -/
def cell142 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 21, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell142_check_hints : cell142.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell142_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell142_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell142_check_hints

theorem cell142_check :
    cell142.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 21, 5, 14] witnessGeometryChecked (by decide))
      cell142_check_indexed

/-- Closed-cover cell 143 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 21, 5, 16]`; `cell143_check` verifies
its explicit-potential certificate. -/
def cell143 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 21, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell143_check_hints : cell143.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22,
     24]] = true := by
  decide +kernel

private theorem cell143_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell143_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell143_check_hints

theorem cell143_check :
    cell143.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 21, 5, 16] witnessGeometryChecked (by decide))
      cell143_check_indexed

/-- Closed-cover cell 144 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 21, 5, 13]`; `cell144_check` verifies
its explicit-potential certificate. -/
def cell144 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 21, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell144_check_hints : cell144.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell144_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell144_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell144_check_hints

theorem cell144_check :
    cell144.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 21, 5, 13] witnessGeometryChecked (by decide))
      cell144_check_indexed

/-- Closed-cover cell 145 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 21, 5, 14]`; `cell145_check` verifies
its explicit-potential certificate. -/
def cell145 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 21, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell145_check_hints : cell145.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6,
     24]] = true := by
  decide +kernel

private theorem cell145_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell145_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell145_check_hints

theorem cell145_check :
    cell145.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 21, 5, 14] witnessGeometryChecked (by decide))
      cell145_check_indexed

/-- Closed-cover cell 146 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 21, 5, 16]`; `cell146_check` verifies
its explicit-potential certificate. -/
def cell146 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 21, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell146_check_hints : cell146.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22,
     24]] = true := by
  decide +kernel

private theorem cell146_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell146_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell146_check_hints

theorem cell146_check :
    cell146.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 21, 5, 16] witnessGeometryChecked (by decide))
      cell146_check_indexed

/-- Closed-cover cell 147 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 21, 5, 13]`; `cell147_check` verifies
its explicit-potential certificate. -/
def cell147 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 21, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell147_check_hints : cell147.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell147_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell147_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell147_check_hints

theorem cell147_check :
    cell147.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 21, 5, 13] witnessGeometryChecked (by decide))
      cell147_check_indexed

/-- Closed-cover cell 148 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 21, 5, 14]`; `cell148_check` verifies
its explicit-potential certificate. -/
def cell148 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 21, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell148_check_hints : cell148.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell148_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell148_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell148_check_hints

theorem cell148_check :
    cell148.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 21, 5, 14] witnessGeometryChecked (by decide))
      cell148_check_indexed

/-- Closed-cover cell 149 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 21, 5, 16]`; `cell149_check` verifies
its explicit-potential certificate. -/
def cell149 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 21, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell149_check_hints : cell149.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22, 24]]
     = true := by
  decide +kernel

private theorem cell149_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell149_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell149_check_hints

theorem cell149_check :
    cell149.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 21, 5, 16] witnessGeometryChecked (by decide))
      cell149_check_indexed

/-- Closed-cover cell 150 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 5, 6]`; `cell150_check` verifies its
explicit-potential certificate. -/
def cell150 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell150_check_hints : cell150.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 18]] = true := by
  decide +kernel

private theorem cell150_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell150_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell150_check_hints

theorem cell150_check :
    cell150.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 5, 6] witnessGeometryChecked (by decide))
      cell150_check_indexed

/-- Closed-cover cell 151 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 5, 6]`; `cell151_check` verifies its
explicit-potential certificate. -/
def cell151 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell151_check_hints : cell151.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell151_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell151_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell151_check_hints

theorem cell151_check :
    cell151.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 5, 6] witnessGeometryChecked (by decide))
      cell151_check_indexed

/-- Closed-cover cell 152 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 5, 6]`; `cell152_check` verifies its
explicit-potential certificate. -/
def cell152 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell152_check_hints : cell152.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell152_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell152_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell152_check_hints

theorem cell152_check :
    cell152.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 5, 6] witnessGeometryChecked (by decide))
      cell152_check_indexed

/-- Closed-cover cell 153 for the fixed row-06 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 25, 4, 5, 6]`; `cell153_check` verifies its
explicit-potential certificate. -/
def cell153 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 25, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell153_check_hints : cell153.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 13, 14, 15, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0,
     0, 0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 19]] = true := by
  decide +kernel

private theorem cell153_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell153_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell153_check_hints

theorem cell153_check :
    cell153.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 25, 4, 5, 6] witnessGeometryChecked (by decide))
      cell153_check_indexed

/-- Closed-cover cell 154 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 5, 6]`; `cell154_check` verifies its
explicit-potential certificate. -/
def cell154 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell154_check_hints : cell154.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell154_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell154_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell154_check_hints

theorem cell154_check :
    cell154.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 5, 6] witnessGeometryChecked (by decide))
      cell154_check_indexed

/-- Closed-cover cell 155 for the fixed row-06 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 5, 6]`; `cell155_check` verifies its
explicit-potential certificate. -/
def cell155 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell155_check_hints : cell155.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 19]] = true := by
  decide +kernel

private theorem cell155_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell155_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell155_check_hints

theorem cell155_check :
    cell155.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 5, 6] witnessGeometryChecked (by decide))
      cell155_check_indexed

/-- Closed-cover cell 156 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 5, 6]`; `cell156_check` verifies its
explicit-potential certificate. -/
def cell156 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell156_check_hints : cell156.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 18]] = true := by
  decide +kernel

private theorem cell156_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell156_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell156_check_hints

theorem cell156_check :
    cell156.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 5, 6] witnessGeometryChecked (by decide))
      cell156_check_indexed

/-- Closed-cover cell 157 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 5, 6]`; `cell157_check` verifies its
explicit-potential certificate. -/
def cell157 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell157_check_hints : cell157.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell157_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell157_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell157_check_hints

theorem cell157_check :
    cell157.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 5, 6] witnessGeometryChecked (by decide))
      cell157_check_indexed

/-- Closed-cover cell 158 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 5, 6]`; `cell158_check` verifies
its explicit-potential certificate. -/
def cell158 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell158_check_hints : cell158.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell158_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell158_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell158_check_hints

theorem cell158_check :
    cell158.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 5, 6] witnessGeometryChecked (by decide))
      cell158_check_indexed

/-- Closed-cover cell 159 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 5, 6]`; `cell159_check` verifies
its explicit-potential certificate. -/
def cell159 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell159_check_hints : cell159.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]] = true := by
  decide +kernel

private theorem cell159_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell159_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell159_check_hints

theorem cell159_check :
    cell159.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 5, 6] witnessGeometryChecked (by decide))
      cell159_check_indexed

/-- Closed-cover cell 160 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 5, 6]`; `cell160_check` verifies its
explicit-potential certificate. -/
def cell160 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell160_check_hints : cell160.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell160_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell160_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell160_check_hints

theorem cell160_check :
    cell160.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 5, 6] witnessGeometryChecked (by decide))
      cell160_check_indexed

/-- Closed-cover cell 161 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 5, 6]`; `cell161_check` verifies its
explicit-potential certificate. -/
def cell161 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell161_check_hints : cell161.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell161_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell161_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell161_check_hints

theorem cell161_check :
    cell161.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 5, 6] witnessGeometryChecked (by decide))
      cell161_check_indexed

/-- Closed-cover cell 162 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 5, 6]`; `cell162_check` verifies its
explicit-potential certificate. -/
def cell162 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell162_check_hints : cell162.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell162_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell162_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell162_check_hints

theorem cell162_check :
    cell162.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 5, 6] witnessGeometryChecked (by decide))
      cell162_check_indexed

/-- Closed-cover cell 163 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 5, 6]`; `cell163_check` verifies
its explicit-potential certificate. -/
def cell163 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell163_check_hints : cell163.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell163_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell163_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell163_check_hints

theorem cell163_check :
    cell163.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 5, 6] witnessGeometryChecked (by decide))
      cell163_check_indexed

/-- Closed-cover cell 164 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 5, 6]`; `cell164_check` verifies
its explicit-potential certificate. -/
def cell164 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell164_check_hints : cell164.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell164_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell164_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell164_check_hints

theorem cell164_check :
    cell164.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 5, 6] witnessGeometryChecked (by decide))
      cell164_check_indexed

/-- Closed-cover cell 165 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 24, 4, 5, 6]`; `cell165_check` verifies its
explicit-potential certificate. -/
def cell165 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 24, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell165_check_hints : cell165.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell165_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell165_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell165_check_hints

theorem cell165_check :
    cell165.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 24, 4, 5, 6] witnessGeometryChecked (by decide))
      cell165_check_indexed

/-- Closed-cover cell 166 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 5, 6]`; `cell166_check` verifies its
explicit-potential certificate. -/
def cell166 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell166_check_hints : cell166.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell166_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell166_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell166_check_hints

theorem cell166_check :
    cell166.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 5, 6] witnessGeometryChecked (by decide))
      cell166_check_indexed

/-- Closed-cover cell 167 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 5, 6]`; `cell167_check` verifies its
explicit-potential certificate. -/
def cell167 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell167_check_hints : cell167.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell167_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell167_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell167_check_hints

theorem cell167_check :
    cell167.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 5, 6] witnessGeometryChecked (by decide))
      cell167_check_indexed

/-- Closed-cover cell 168 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 5, 6]`; `cell168_check` verifies
its explicit-potential certificate. -/
def cell168 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell168_check_hints : cell168.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell168_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell168_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell168_check_hints

theorem cell168_check :
    cell168.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 5, 6] witnessGeometryChecked (by decide))
      cell168_check_indexed

/-- Closed-cover cell 169 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 5, 6]`; `cell169_check` verifies
its explicit-potential certificate. -/
def cell169 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell169_check_hints : cell169.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell169_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell169_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell169_check_hints

theorem cell169_check :
    cell169.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 5, 6] witnessGeometryChecked (by decide))
      cell169_check_indexed

/-- Closed-cover cell 170 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 26, 4, 5, 6]`; `cell170_check` verifies its
explicit-potential certificate. -/
def cell170 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 26, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell170_check_hints : cell170.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 16, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell170_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell170_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell170_check_hints

theorem cell170_check :
    cell170.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 26, 4, 5, 6] witnessGeometryChecked (by decide))
      cell170_check_indexed

/-- Closed-cover cell 171 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 5, 6]`; `cell171_check` verifies its
explicit-potential certificate. -/
def cell171 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell171_check_hints : cell171.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell171_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell171_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell171_check_hints

theorem cell171_check :
    cell171.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 5, 6] witnessGeometryChecked (by decide))
      cell171_check_indexed

/-- Closed-cover cell 172 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 5, 6]`; `cell172_check` verifies its
explicit-potential certificate. -/
def cell172 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell172_check_hints : cell172.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell172_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell172_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell172_check_hints

theorem cell172_check :
    cell172.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 5, 6] witnessGeometryChecked (by decide))
      cell172_check_indexed

/-- Closed-cover cell 173 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 5, 6]`; `cell173_check` verifies
its explicit-potential certificate. -/
def cell173 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell173_check_hints : cell173.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell173_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell173_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell173_check_hints

theorem cell173_check :
    cell173.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 5, 6] witnessGeometryChecked (by decide))
      cell173_check_indexed

/-- Closed-cover cell 174 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 5, 6]`; `cell174_check` verifies
its explicit-potential certificate. -/
def cell174 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 5, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell174_check_hints : cell174.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell174_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell174_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell174_check_hints

theorem cell174_check :
    cell174.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 5, 6] witnessGeometryChecked (by decide))
      cell174_check_indexed

/-- Closed-cover cell 175 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 5, 12]`; `cell175_check` verifies
its explicit-potential certificate. -/
def cell175 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell175_check_hints : cell175.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 18]] = true := by
  decide +kernel

private theorem cell175_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell175_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell175_check_hints

theorem cell175_check :
    cell175.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 5, 12] witnessGeometryChecked (by decide))
      cell175_check_indexed

/-- Closed-cover cell 176 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 5, 13]`; `cell176_check` verifies
its explicit-potential certificate. -/
def cell176 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell176_check_hints : cell176.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 6, 20]] = true := by
  decide +kernel

private theorem cell176_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell176_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell176_check_hints

theorem cell176_check :
    cell176.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 5, 13] witnessGeometryChecked (by decide))
      cell176_check_indexed

/-- Closed-cover cell 177 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 5, 14]`; `cell177_check` verifies
its explicit-potential certificate. -/
def cell177 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell177_check_hints : cell177.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 6, 20]] = true := by
  decide +kernel

private theorem cell177_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell177_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell177_check_hints

theorem cell177_check :
    cell177.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 5, 14] witnessGeometryChecked (by decide))
      cell177_check_indexed

/-- Closed-cover cell 178 for the fixed row-06 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 5, 15]`; `cell178_check` verifies
its explicit-potential certificate. -/
def cell178 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 5, 15] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell178_check_hints : cell178.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 13, 14,
     13, 14]] = true := by
  decide +kernel

private theorem cell178_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell178_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell178_check_hints

theorem cell178_check :
    cell178.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 5, 15] witnessGeometryChecked (by decide))
      cell178_check_indexed

/-- Closed-cover cell 179 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 5, 16]`; `cell179_check` verifies
its explicit-potential certificate. -/
def cell179 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell179_check_hints : cell179.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 18, 20]] = true := by
  decide +kernel

private theorem cell179_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell179_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell179_check_hints

theorem cell179_check :
    cell179.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 5, 16] witnessGeometryChecked (by decide))
      cell179_check_indexed

/-- Closed-cover cell 180 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 5, 12]`; `cell180_check` verifies
its explicit-potential certificate. -/
def cell180 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell180_check_hints : cell180.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell180_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell180_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell180_check_hints

theorem cell180_check :
    cell180.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 5, 12] witnessGeometryChecked (by decide))
      cell180_check_indexed

/-- Closed-cover cell 181 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 5, 13]`; `cell181_check` verifies
its explicit-potential certificate. -/
def cell181 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell181_check_hints : cell181.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell181_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell181_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell181_check_hints

theorem cell181_check :
    cell181.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 5, 13] witnessGeometryChecked (by decide))
      cell181_check_indexed

/-- Closed-cover cell 182 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 5, 14]`; `cell182_check` verifies
its explicit-potential certificate. -/
def cell182 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell182_check_hints : cell182.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell182_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell182_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell182_check_hints

theorem cell182_check :
    cell182.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 5, 14] witnessGeometryChecked (by decide))
      cell182_check_indexed

/-- Closed-cover cell 183 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 5, 15]`; `cell183_check` verifies
its explicit-potential certificate. -/
def cell183 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 5, 15] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell183_check_hints : cell183.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20,
     21, 0, 0, 0, 0, 13, 14, 13, 14]] = true := by
  decide +kernel

private theorem cell183_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell183_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell183_check_hints

theorem cell183_check :
    cell183.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 5, 15] witnessGeometryChecked (by decide))
      cell183_check_indexed

/-- Closed-cover cell 184 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 5, 16]`; `cell184_check` verifies
its explicit-potential certificate. -/
def cell184 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell184_check_hints : cell184.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell184_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell184_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell184_check_hints

theorem cell184_check :
    cell184.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 5, 16] witnessGeometryChecked (by decide))
      cell184_check_indexed

/-- Closed-cover cell 185 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 5, 12]`; `cell185_check` verifies
its explicit-potential certificate. -/
def cell185 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell185_check_hints : cell185.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell185_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell185_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell185_check_hints

theorem cell185_check :
    cell185.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 5, 12] witnessGeometryChecked (by decide))
      cell185_check_indexed

/-- Closed-cover cell 186 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 5, 13]`; `cell186_check` verifies
its explicit-potential certificate. -/
def cell186 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell186_check_hints : cell186.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell186_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell186_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell186_check_hints

theorem cell186_check :
    cell186.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 5, 13] witnessGeometryChecked (by decide))
      cell186_check_indexed

/-- Closed-cover cell 187 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 5, 14]`; `cell187_check` verifies
its explicit-potential certificate. -/
def cell187 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell187_check_hints : cell187.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell187_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell187_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell187_check_hints

theorem cell187_check :
    cell187.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 5, 14] witnessGeometryChecked (by decide))
      cell187_check_indexed

/-- Closed-cover cell 188 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 5, 15]`; `cell188_check` verifies
its explicit-potential certificate. -/
def cell188 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 5, 15] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell188_check_hints : cell188.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20,
     21, 0, 0, 0, 0, 13, 14, 13, 14]] = true := by
  decide +kernel

private theorem cell188_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell188_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell188_check_hints

theorem cell188_check :
    cell188.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 5, 15] witnessGeometryChecked (by decide))
      cell188_check_indexed

/-- Closed-cover cell 189 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 5, 16]`; `cell189_check` verifies
its explicit-potential certificate. -/
def cell189 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell189_check_hints : cell189.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell189_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell189_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell189_check_hints

theorem cell189_check :
    cell189.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 5, 16] witnessGeometryChecked (by decide))
      cell189_check_indexed

/-- Closed-cover cell 190 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 5, 12]`; `cell190_check` verifies
its explicit-potential certificate. -/
def cell190 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell190_check_hints : cell190.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell190_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell190_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell190_check_hints

theorem cell190_check :
    cell190.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 5, 12] witnessGeometryChecked (by decide))
      cell190_check_indexed

/-- Closed-cover cell 191 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 5, 13]`; `cell191_check` verifies
its explicit-potential certificate. -/
def cell191 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell191_check_hints : cell191.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell191_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell191_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell191_check_hints

theorem cell191_check :
    cell191.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 5, 13] witnessGeometryChecked (by decide))
      cell191_check_indexed

/-- Closed-cover cell 192 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 5, 14]`; `cell192_check` verifies
its explicit-potential certificate. -/
def cell192 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell192_check_hints : cell192.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell192_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell192_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell192_check_hints

theorem cell192_check :
    cell192.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 5, 14] witnessGeometryChecked (by decide))
      cell192_check_indexed

/-- Closed-cover cell 193 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 5, 15]`; `cell193_check` verifies
its explicit-potential certificate. -/
def cell193 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 5, 15] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell193_check_hints : cell193.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20,
     21, 0, 0, 0, 0, 13, 14, 13, 14]] = true := by
  decide +kernel

private theorem cell193_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell193_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell193_check_hints

theorem cell193_check :
    cell193.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 5, 15] witnessGeometryChecked (by decide))
      cell193_check_indexed

/-- The ordered row-06 closed-cover cell block with global indices 97 through 193, used when
assembling the full 483-cell cover. -/
def chunk : List (CoordinateCell row06Core) :=
  [cell97, cell98, cell99, cell100, cell101, cell102, cell103, cell104, cell105, cell106, cell107,
  cell108, cell109, cell110, cell111, cell112, cell113, cell114, cell115, cell116, cell117, cell118,
  cell119, cell120, cell121, cell122, cell123, cell124, cell125, cell126, cell127, cell128, cell129,
  cell130, cell131, cell132, cell133, cell134, cell135, cell136, cell137, cell138, cell139, cell140,
  cell141, cell142, cell143, cell144, cell145, cell146, cell147, cell148, cell149, cell150, cell151,
  cell152, cell153, cell154, cell155, cell156, cell157, cell158, cell159, cell160, cell161, cell162,
  cell163, cell164, cell165, cell166, cell167, cell168, cell169, cell170, cell171, cell172, cell173,
  cell174, cell175, cell176, cell177, cell178, cell179, cell180, cell181, cell182, cell183, cell184,
  cell185, cell186, cell187, cell188, cell189, cell190, cell191, cell192, cell193]

theorem chunk_check :
    chunk.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [chunk, cell97_check, cell98_check, cell99_check, cell100_check, cell101_check,
    cell102_check, cell103_check, cell104_check, cell105_check, cell106_check, cell107_check,
    cell108_check, cell109_check, cell110_check, cell111_check, cell112_check, cell113_check,
    cell114_check, cell115_check, cell116_check, cell117_check, cell118_check, cell119_check,
    cell120_check, cell121_check, cell122_check, cell123_check, cell124_check, cell125_check,
    cell126_check, cell127_check, cell128_check, cell129_check, cell130_check, cell131_check,
    cell132_check, cell133_check, cell134_check, cell135_check, cell136_check, cell137_check,
    cell138_check, cell139_check, cell140_check, cell141_check, cell142_check, cell143_check,
    cell144_check, cell145_check, cell146_check, cell147_check, cell148_check, cell149_check,
    cell150_check, cell151_check, cell152_check, cell153_check, cell154_check, cell155_check,
    cell156_check, cell157_check, cell158_check, cell159_check, cell160_check, cell161_check,
    cell162_check, cell163_check, cell164_check, cell165_check, cell166_check, cell167_check,
    cell168_check, cell169_check, cell170_check, cell171_check, cell172_check, cell173_check,
    cell174_check, cell175_check, cell176_check, cell177_check, cell178_check, cell179_check,
    cell180_check, cell181_check, cell182_check, cell183_check, cell184_check, cell185_check,
    cell186_check, cell187_check, cell188_check, cell189_check, cell190_check, cell191_check,
    cell192_check, cell193_check]

end AtanasovRanganathan.GenusFiveRow06CoverCells1
