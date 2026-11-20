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

Generated cell chunk 4 of 5 for the AR row-06 chamber cover
(cells 387-482).  Split across modules because the kernel cost of
replaying a cell is cumulative within one Lean process. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06CoverCells4

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow06CoverBase

/-- Closed-cover cell 387 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 21, 29, 6]`; `cell387_check` verifies
its explicit-potential certificate. -/
def cell387 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 21, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell387_check_hints : cell387.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell387_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell387_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell387_check_hints

theorem cell387_check :
    cell387.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 21, 29, 6] witnessGeometryChecked (by decide))
      cell387_check_indexed

/-- Closed-cover cell 388 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 21, 30, 6]`; `cell388_check` verifies
its explicit-potential certificate. -/
def cell388 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 21, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell388_check_hints : cell388.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 24]] = true := by
  decide +kernel

private theorem cell388_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell388_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell388_check_hints

theorem cell388_check :
    cell388.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 21, 30, 6] witnessGeometryChecked (by decide))
      cell388_check_indexed

/-- Closed-cover cell 389 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 27, 6]`; `cell389_check` verifies
its explicit-potential certificate. -/
def cell389 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell389_check_hints : cell389.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 18]] = true := by
  decide +kernel

private theorem cell389_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell389_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell389_check_hints

theorem cell389_check :
    cell389.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 27, 6] witnessGeometryChecked (by decide))
      cell389_check_indexed

/-- Closed-cover cell 390 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 28, 6]`; `cell390_check` verifies
its explicit-potential certificate. -/
def cell390 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell390_check_hints : cell390.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell390_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell390_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell390_check_hints

theorem cell390_check :
    cell390.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 28, 6] witnessGeometryChecked (by decide))
      cell390_check_indexed

/-- Closed-cover cell 391 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 29, 6]`; `cell391_check` verifies
its explicit-potential certificate. -/
def cell391 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell391_check_hints : cell391.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell391_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell391_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell391_check_hints

theorem cell391_check :
    cell391.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 29, 6] witnessGeometryChecked (by decide))
      cell391_check_indexed

/-- Closed-cover cell 392 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 22, 4, 30, 6]`; `cell392_check` verifies
its explicit-potential certificate. -/
def cell392 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 22, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell392_check_hints : cell392.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell392_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell392_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell392_check_hints

theorem cell392_check :
    cell392.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 22, 4, 30, 6] witnessGeometryChecked (by decide))
      cell392_check_indexed

/-- Closed-cover cell 393 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 27, 6]`; `cell393_check` verifies
its explicit-potential certificate. -/
def cell393 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell393_check_hints : cell393.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell393_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell393_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell393_check_hints

theorem cell393_check :
    cell393.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 27, 6] witnessGeometryChecked (by decide))
      cell393_check_indexed

/-- Closed-cover cell 394 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 28, 6]`; `cell394_check` verifies
its explicit-potential certificate. -/
def cell394 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell394_check_hints : cell394.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell394_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell394_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell394_check_hints

theorem cell394_check :
    cell394.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 28, 6] witnessGeometryChecked (by decide))
      cell394_check_indexed

/-- Closed-cover cell 395 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 29, 6]`; `cell395_check` verifies
its explicit-potential certificate. -/
def cell395 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell395_check_hints : cell395.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell395_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell395_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell395_check_hints

theorem cell395_check :
    cell395.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 29, 6] witnessGeometryChecked (by decide))
      cell395_check_indexed

/-- Closed-cover cell 396 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 23, 4, 30, 6]`; `cell396_check` verifies
its explicit-potential certificate. -/
def cell396 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 23, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell396_check_hints : cell396.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell396_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell396_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell396_check_hints

theorem cell396_check :
    cell396.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 23, 4, 30, 6] witnessGeometryChecked (by decide))
      cell396_check_indexed

/-- Closed-cover cell 397 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 27, 6]`; `cell397_check` verifies
its explicit-potential certificate. -/
def cell397 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell397_check_hints : cell397.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell397_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell397_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell397_check_hints

theorem cell397_check :
    cell397.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 27, 6] witnessGeometryChecked (by decide))
      cell397_check_indexed

/-- Closed-cover cell 398 for the fixed row-06 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 25, 4, 27, 6]`; `cell398_check` verifies
its explicit-potential certificate. -/
def cell398 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 25, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell398_check_hints : cell398.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 13, 14, 15, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0,
     0, 0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 19]] = true := by
  decide +kernel

private theorem cell398_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell398_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell398_check_hints

theorem cell398_check :
    cell398.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 25, 4, 27, 6] witnessGeometryChecked (by decide))
      cell398_check_indexed

/-- Closed-cover cell 399 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 27, 6]`; `cell399_check` verifies
its explicit-potential certificate. -/
def cell399 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell399_check_hints : cell399.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell399_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell399_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell399_check_hints

theorem cell399_check :
    cell399.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 27, 6] witnessGeometryChecked (by decide))
      cell399_check_indexed

/-- Closed-cover cell 400 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 28, 6]`; `cell400_check` verifies
its explicit-potential certificate. -/
def cell400 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell400_check_hints : cell400.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell400_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell400_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell400_check_hints

theorem cell400_check :
    cell400.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 28, 6] witnessGeometryChecked (by decide))
      cell400_check_indexed

/-- Closed-cover cell 401 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 25, 4, 28, 6]`; `cell401_check` verifies
its explicit-potential certificate. -/
def cell401 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 25, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell401_check_hints : cell401.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 13, 14, 15, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 6, 19, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell401_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell401_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell401_check_hints

theorem cell401_check :
    cell401.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 25, 4, 28, 6] witnessGeometryChecked (by decide))
      cell401_check_indexed

/-- Closed-cover cell 402 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 28, 6]`; `cell402_check` verifies
its explicit-potential certificate. -/
def cell402 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell402_check_hints : cell402.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell402_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell402_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell402_check_hints

theorem cell402_check :
    cell402.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 28, 6] witnessGeometryChecked (by decide))
      cell402_check_indexed

/-- Closed-cover cell 403 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 29, 6]`; `cell403_check` verifies
its explicit-potential certificate. -/
def cell403 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell403_check_hints : cell403.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell403_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell403_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell403_check_hints

theorem cell403_check :
    cell403.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 29, 6] witnessGeometryChecked (by decide))
      cell403_check_indexed

/-- Closed-cover cell 404 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 25, 4, 29, 6]`; `cell404_check` verifies
its explicit-potential certificate. -/
def cell404 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 25, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell404_check_hints : cell404.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 13, 14, 15, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 6, 19, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell404_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell404_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell404_check_hints

theorem cell404_check :
    cell404.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 25, 4, 29, 6] witnessGeometryChecked (by decide))
      cell404_check_indexed

/-- Closed-cover cell 405 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 29, 6]`; `cell405_check` verifies
its explicit-potential certificate. -/
def cell405 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell405_check_hints : cell405.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell405_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell405_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell405_check_hints

theorem cell405_check :
    cell405.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 29, 6] witnessGeometryChecked (by decide))
      cell405_check_indexed

/-- Closed-cover cell 406 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 24, 4, 30, 6]`; `cell406_check` verifies
its explicit-potential certificate. -/
def cell406 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 24, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell406_check_hints : cell406.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell406_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell406_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell406_check_hints

theorem cell406_check :
    cell406.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 24, 4, 30, 6] witnessGeometryChecked (by decide))
      cell406_check_indexed

/-- Closed-cover cell 407 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 30, 6]`; `cell407_check` verifies
its explicit-potential certificate. -/
def cell407 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell407_check_hints : cell407.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell407_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell407_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell407_check_hints

theorem cell407_check :
    cell407.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 30, 6] witnessGeometryChecked (by decide))
      cell407_check_indexed

/-- Closed-cover cell 408 for the fixed row-06 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 27, 6]`; `cell408_check` verifies
its explicit-potential certificate. -/
def cell408 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell408_check_hints : cell408.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 19]] = true := by
  decide +kernel

private theorem cell408_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell408_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell408_check_hints

theorem cell408_check :
    cell408.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 27, 6] witnessGeometryChecked (by decide))
      cell408_check_indexed

/-- Closed-cover cell 409 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 27, 6]`; `cell409_check` verifies
its explicit-potential certificate. -/
def cell409 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell409_check_hints : cell409.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 18]] = true := by
  decide +kernel

private theorem cell409_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell409_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell409_check_hints

theorem cell409_check :
    cell409.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 27, 6] witnessGeometryChecked (by decide))
      cell409_check_indexed

/-- Closed-cover cell 410 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 27, 6]`; `cell410_check` verifies
its explicit-potential certificate. -/
def cell410 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell410_check_hints : cell410.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell410_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell410_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell410_check_hints

theorem cell410_check :
    cell410.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 27, 6] witnessGeometryChecked (by decide))
      cell410_check_indexed

/-- Closed-cover cell 411 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 27, 6]`; `cell411_check` verifies
its explicit-potential certificate. -/
def cell411 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell411_check_hints : cell411.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell411_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell411_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell411_check_hints

theorem cell411_check :
    cell411.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 27, 6] witnessGeometryChecked (by decide))
      cell411_check_indexed

/-- Closed-cover cell 412 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 27, 6]`; `cell412_check` verifies
its explicit-potential certificate. -/
def cell412 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell412_check_hints : cell412.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]] = true := by
  decide +kernel

private theorem cell412_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell412_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell412_check_hints

theorem cell412_check :
    cell412.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 27, 6] witnessGeometryChecked (by decide))
      cell412_check_indexed

/-- Closed-cover cell 413 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 28, 6]`; `cell413_check` verifies
its explicit-potential certificate. -/
def cell413 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell413_check_hints : cell413.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 6, 19, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21]]
     = true := by
  decide +kernel

private theorem cell413_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell413_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell413_check_hints

theorem cell413_check :
    cell413.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 28, 6] witnessGeometryChecked (by decide))
      cell413_check_indexed

/-- Closed-cover cell 414 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 28, 6]`; `cell414_check` verifies
its explicit-potential certificate. -/
def cell414 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell414_check_hints : cell414.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell414_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell414_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell414_check_hints

theorem cell414_check :
    cell414.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 28, 6] witnessGeometryChecked (by decide))
      cell414_check_indexed

/-- Closed-cover cell 415 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 28, 6]`; `cell415_check` verifies
its explicit-potential certificate. -/
def cell415 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell415_check_hints : cell415.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell415_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell415_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell415_check_hints

theorem cell415_check :
    cell415.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 28, 6] witnessGeometryChecked (by decide))
      cell415_check_indexed

/-- Closed-cover cell 416 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 28, 6]`; `cell416_check` verifies
its explicit-potential certificate. -/
def cell416 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell416_check_hints : cell416.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell416_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell416_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell416_check_hints

theorem cell416_check :
    cell416.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 28, 6] witnessGeometryChecked (by decide))
      cell416_check_indexed

/-- Closed-cover cell 417 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 28, 6]`; `cell417_check` verifies
its explicit-potential certificate. -/
def cell417 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell417_check_hints : cell417.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell417_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell417_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell417_check_hints

theorem cell417_check :
    cell417.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 28, 6] witnessGeometryChecked (by decide))
      cell417_check_indexed

/-- Closed-cover cell 418 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 29, 6]`; `cell418_check` verifies
its explicit-potential certificate. -/
def cell418 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell418_check_hints : cell418.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 6, 19, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21]]
     = true := by
  decide +kernel

private theorem cell418_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell418_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell418_check_hints

theorem cell418_check :
    cell418.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 29, 6] witnessGeometryChecked (by decide))
      cell418_check_indexed

/-- Closed-cover cell 419 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 29, 6]`; `cell419_check` verifies
its explicit-potential certificate. -/
def cell419 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell419_check_hints : cell419.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell419_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell419_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell419_check_hints

theorem cell419_check :
    cell419.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 29, 6] witnessGeometryChecked (by decide))
      cell419_check_indexed

/-- Closed-cover cell 420 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 29, 6]`; `cell420_check` verifies
its explicit-potential certificate. -/
def cell420 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell420_check_hints : cell420.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell420_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell420_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell420_check_hints

theorem cell420_check :
    cell420.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 29, 6] witnessGeometryChecked (by decide))
      cell420_check_indexed

/-- Closed-cover cell 421 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 29, 6]`; `cell421_check` verifies
its explicit-potential certificate. -/
def cell421 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell421_check_hints : cell421.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell421_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell421_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell421_check_hints

theorem cell421_check :
    cell421.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 29, 6] witnessGeometryChecked (by decide))
      cell421_check_indexed

/-- Closed-cover cell 422 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 29, 6]`; `cell422_check` verifies
its explicit-potential certificate. -/
def cell422 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell422_check_hints : cell422.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell422_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell422_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell422_check_hints

theorem cell422_check :
    cell422.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 29, 6] witnessGeometryChecked (by decide))
      cell422_check_indexed

/-- Closed-cover cell 423 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 30, 6]`; `cell423_check` verifies
its explicit-potential certificate. -/
def cell423 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell423_check_hints : cell423.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 18, 19, 20, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21]]
     = true := by
  decide +kernel

private theorem cell423_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell423_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell423_check_hints

theorem cell423_check :
    cell423.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 30, 6] witnessGeometryChecked (by decide))
      cell423_check_indexed

/-- Closed-cover cell 424 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 30, 6]`; `cell424_check` verifies
its explicit-potential certificate. -/
def cell424 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell424_check_hints : cell424.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell424_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell424_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell424_check_hints

theorem cell424_check :
    cell424.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 30, 6] witnessGeometryChecked (by decide))
      cell424_check_indexed

/-- Closed-cover cell 425 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 30, 6]`; `cell425_check` verifies
its explicit-potential certificate. -/
def cell425 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell425_check_hints : cell425.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     22]] = true := by
  decide +kernel

private theorem cell425_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell425_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell425_check_hints

theorem cell425_check :
    cell425.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 30, 6] witnessGeometryChecked (by decide))
      cell425_check_indexed

/-- Closed-cover cell 426 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 30, 6]`; `cell426_check` verifies
its explicit-potential certificate. -/
def cell426 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell426_check_hints : cell426.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     22]] = true := by
  decide +kernel

private theorem cell426_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell426_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell426_check_hints

theorem cell426_check :
    cell426.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 30, 6] witnessGeometryChecked (by decide))
      cell426_check_indexed

/-- Closed-cover cell 427 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 30, 6]`; `cell427_check` verifies
its explicit-potential certificate. -/
def cell427 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell427_check_hints : cell427.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell427_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell427_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell427_check_hints

theorem cell427_check :
    cell427.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 30, 6] witnessGeometryChecked (by decide))
      cell427_check_indexed

/-- Closed-cover cell 428 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 27, 6]`; `cell428_check` verifies
its explicit-potential certificate. -/
def cell428 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell428_check_hints : cell428.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell428_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell428_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell428_check_hints

theorem cell428_check :
    cell428.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 27, 6] witnessGeometryChecked (by decide))
      cell428_check_indexed

/-- Closed-cover cell 429 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 27, 6]`; `cell429_check` verifies
its explicit-potential certificate. -/
def cell429 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell429_check_hints : cell429.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell429_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell429_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell429_check_hints

theorem cell429_check :
    cell429.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 27, 6] witnessGeometryChecked (by decide))
      cell429_check_indexed

/-- Closed-cover cell 430 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 27, 6]`; `cell430_check` verifies
its explicit-potential certificate. -/
def cell430 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell430_check_hints : cell430.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell430_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell430_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell430_check_hints

theorem cell430_check :
    cell430.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 27, 6] witnessGeometryChecked (by decide))
      cell430_check_indexed

/-- Closed-cover cell 431 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 27, 6]`; `cell431_check` verifies
its explicit-potential certificate. -/
def cell431 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell431_check_hints : cell431.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell431_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell431_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell431_check_hints

theorem cell431_check :
    cell431.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 27, 6] witnessGeometryChecked (by decide))
      cell431_check_indexed

/-- Closed-cover cell 432 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 27, 6]`; `cell432_check` verifies
its explicit-potential certificate. -/
def cell432 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell432_check_hints : cell432.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell432_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell432_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell432_check_hints

theorem cell432_check :
    cell432.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 27, 6] witnessGeometryChecked (by decide))
      cell432_check_indexed

/-- Closed-cover cell 433 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 28, 6]`; `cell433_check` verifies
its explicit-potential certificate. -/
def cell433 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell433_check_hints : cell433.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 6, 21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 23]] = true := by
  decide +kernel

private theorem cell433_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell433_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell433_check_hints

theorem cell433_check :
    cell433.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 28, 6] witnessGeometryChecked (by decide))
      cell433_check_indexed

/-- Closed-cover cell 434 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 28, 6]`; `cell434_check` verifies
its explicit-potential certificate. -/
def cell434 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell434_check_hints : cell434.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell434_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell434_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell434_check_hints

theorem cell434_check :
    cell434.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 28, 6] witnessGeometryChecked (by decide))
      cell434_check_indexed

/-- Closed-cover cell 435 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 28, 6]`; `cell435_check` verifies
its explicit-potential certificate. -/
def cell435 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell435_check_hints : cell435.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell435_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell435_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell435_check_hints

theorem cell435_check :
    cell435.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 28, 6] witnessGeometryChecked (by decide))
      cell435_check_indexed

/-- Closed-cover cell 436 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 28, 6]`; `cell436_check` verifies
its explicit-potential certificate. -/
def cell436 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell436_check_hints : cell436.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell436_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell436_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell436_check_hints

theorem cell436_check :
    cell436.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 28, 6] witnessGeometryChecked (by decide))
      cell436_check_indexed

/-- Closed-cover cell 437 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 28, 6]`; `cell437_check` verifies
its explicit-potential certificate. -/
def cell437 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell437_check_hints : cell437.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell437_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell437_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell437_check_hints

theorem cell437_check :
    cell437.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 28, 6] witnessGeometryChecked (by decide))
      cell437_check_indexed

/-- Closed-cover cell 438 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 29, 6]`; `cell438_check` verifies
its explicit-potential certificate. -/
def cell438 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell438_check_hints : cell438.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 6, 21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 23]] = true := by
  decide +kernel

private theorem cell438_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell438_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell438_check_hints

theorem cell438_check :
    cell438.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 29, 6] witnessGeometryChecked (by decide))
      cell438_check_indexed

/-- Closed-cover cell 439 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 29, 6]`; `cell439_check` verifies
its explicit-potential certificate. -/
def cell439 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell439_check_hints : cell439.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell439_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell439_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell439_check_hints

theorem cell439_check :
    cell439.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 29, 6] witnessGeometryChecked (by decide))
      cell439_check_indexed

/-- Closed-cover cell 440 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 29, 6]`; `cell440_check` verifies
its explicit-potential certificate. -/
def cell440 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell440_check_hints : cell440.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell440_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell440_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell440_check_hints

theorem cell440_check :
    cell440.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 29, 6] witnessGeometryChecked (by decide))
      cell440_check_indexed

/-- Closed-cover cell 441 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 29, 6]`; `cell441_check` verifies
its explicit-potential certificate. -/
def cell441 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell441_check_hints : cell441.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell441_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell441_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell441_check_hints

theorem cell441_check :
    cell441.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 29, 6] witnessGeometryChecked (by decide))
      cell441_check_indexed

/-- Closed-cover cell 442 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 29, 6]`; `cell442_check` verifies
its explicit-potential certificate. -/
def cell442 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell442_check_hints : cell442.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell442_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell442_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell442_check_hints

theorem cell442_check :
    cell442.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 29, 6] witnessGeometryChecked (by decide))
      cell442_check_indexed

/-- Closed-cover cell 443 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 30, 6]`; `cell443_check` verifies
its explicit-potential certificate. -/
def cell443 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell443_check_hints : cell443.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 22, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 5, 23]] = true := by
  decide +kernel

private theorem cell443_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell443_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell443_check_hints

theorem cell443_check :
    cell443.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 30, 6] witnessGeometryChecked (by decide))
      cell443_check_indexed

/-- Closed-cover cell 444 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 30, 6]`; `cell444_check` verifies
its explicit-potential certificate. -/
def cell444 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell444_check_hints : cell444.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell444_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell444_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell444_check_hints

theorem cell444_check :
    cell444.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 30, 6] witnessGeometryChecked (by decide))
      cell444_check_indexed

/-- Closed-cover cell 445 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 30, 6]`; `cell445_check` verifies
its explicit-potential certificate. -/
def cell445 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell445_check_hints : cell445.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell445_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell445_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell445_check_hints

theorem cell445_check :
    cell445.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 30, 6] witnessGeometryChecked (by decide))
      cell445_check_indexed

/-- Closed-cover cell 446 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 30, 6]`; `cell446_check` verifies
its explicit-potential certificate. -/
def cell446 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell446_check_hints : cell446.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell446_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell446_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell446_check_hints

theorem cell446_check :
    cell446.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 30, 6] witnessGeometryChecked (by decide))
      cell446_check_indexed

/-- Closed-cover cell 447 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 30, 6]`; `cell447_check` verifies
its explicit-potential certificate. -/
def cell447 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell447_check_hints : cell447.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell447_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell447_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell447_check_hints

theorem cell447_check :
    cell447.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 30, 6] witnessGeometryChecked (by decide))
      cell447_check_indexed

/-- Closed-cover cell 448 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 24, 4, 27, 6]`; `cell448_check` verifies
its explicit-potential certificate. -/
def cell448 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 24, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell448_check_hints : cell448.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell448_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell448_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell448_check_hints

theorem cell448_check :
    cell448.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 24, 4, 27, 6] witnessGeometryChecked (by decide))
      cell448_check_indexed

/-- Closed-cover cell 449 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 27, 6]`; `cell449_check` verifies
its explicit-potential certificate. -/
def cell449 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell449_check_hints : cell449.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell449_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell449_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell449_check_hints

theorem cell449_check :
    cell449.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 27, 6] witnessGeometryChecked (by decide))
      cell449_check_indexed

/-- Closed-cover cell 450 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 27, 6]`; `cell450_check` verifies
its explicit-potential certificate. -/
def cell450 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell450_check_hints : cell450.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell450_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell450_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell450_check_hints

theorem cell450_check :
    cell450.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 27, 6] witnessGeometryChecked (by decide))
      cell450_check_indexed

/-- Closed-cover cell 451 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 27, 6]`; `cell451_check` verifies
its explicit-potential certificate. -/
def cell451 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell451_check_hints : cell451.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell451_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell451_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell451_check_hints

theorem cell451_check :
    cell451.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 27, 6] witnessGeometryChecked (by decide))
      cell451_check_indexed

/-- Closed-cover cell 452 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 27, 6]`; `cell452_check` verifies
its explicit-potential certificate. -/
def cell452 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell452_check_hints : cell452.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell452_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell452_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell452_check_hints

theorem cell452_check :
    cell452.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 27, 6] witnessGeometryChecked (by decide))
      cell452_check_indexed

/-- Closed-cover cell 453 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 24, 4, 28, 6]`; `cell453_check` verifies
its explicit-potential certificate. -/
def cell453 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 24, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell453_check_hints : cell453.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 6, 21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 23]] = true := by
  decide +kernel

private theorem cell453_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell453_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell453_check_hints

theorem cell453_check :
    cell453.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 24, 4, 28, 6] witnessGeometryChecked (by decide))
      cell453_check_indexed

/-- Closed-cover cell 454 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 28, 6]`; `cell454_check` verifies
its explicit-potential certificate. -/
def cell454 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell454_check_hints : cell454.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell454_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell454_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell454_check_hints

theorem cell454_check :
    cell454.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 28, 6] witnessGeometryChecked (by decide))
      cell454_check_indexed

/-- Closed-cover cell 455 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 28, 6]`; `cell455_check` verifies
its explicit-potential certificate. -/
def cell455 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell455_check_hints : cell455.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell455_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell455_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell455_check_hints

theorem cell455_check :
    cell455.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 28, 6] witnessGeometryChecked (by decide))
      cell455_check_indexed

/-- Closed-cover cell 456 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 28, 6]`; `cell456_check` verifies
its explicit-potential certificate. -/
def cell456 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell456_check_hints : cell456.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell456_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell456_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell456_check_hints

theorem cell456_check :
    cell456.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 28, 6] witnessGeometryChecked (by decide))
      cell456_check_indexed

/-- Closed-cover cell 457 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 28, 6]`; `cell457_check` verifies
its explicit-potential certificate. -/
def cell457 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell457_check_hints : cell457.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell457_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell457_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell457_check_hints

theorem cell457_check :
    cell457.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 28, 6] witnessGeometryChecked (by decide))
      cell457_check_indexed

/-- Closed-cover cell 458 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 24, 4, 29, 6]`; `cell458_check` verifies
its explicit-potential certificate. -/
def cell458 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 24, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell458_check_hints : cell458.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 6, 21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 23]] = true := by
  decide +kernel

private theorem cell458_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell458_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell458_check_hints

theorem cell458_check :
    cell458.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 24, 4, 29, 6] witnessGeometryChecked (by decide))
      cell458_check_indexed

/-- Closed-cover cell 459 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 29, 6]`; `cell459_check` verifies
its explicit-potential certificate. -/
def cell459 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell459_check_hints : cell459.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell459_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell459_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell459_check_hints

theorem cell459_check :
    cell459.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 29, 6] witnessGeometryChecked (by decide))
      cell459_check_indexed

/-- Closed-cover cell 460 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 29, 6]`; `cell460_check` verifies
its explicit-potential certificate. -/
def cell460 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell460_check_hints : cell460.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell460_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell460_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell460_check_hints

theorem cell460_check :
    cell460.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 29, 6] witnessGeometryChecked (by decide))
      cell460_check_indexed

/-- Closed-cover cell 461 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 29, 6]`; `cell461_check` verifies
its explicit-potential certificate. -/
def cell461 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell461_check_hints : cell461.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell461_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell461_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell461_check_hints

theorem cell461_check :
    cell461.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 29, 6] witnessGeometryChecked (by decide))
      cell461_check_indexed

/-- Closed-cover cell 462 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 29, 6]`; `cell462_check` verifies
its explicit-potential certificate. -/
def cell462 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell462_check_hints : cell462.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell462_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell462_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell462_check_hints

theorem cell462_check :
    cell462.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 29, 6] witnessGeometryChecked (by decide))
      cell462_check_indexed

/-- Closed-cover cell 463 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 30, 6]`; `cell463_check` verifies
its explicit-potential certificate. -/
def cell463 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell463_check_hints : cell463.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell463_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell463_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell463_check_hints

theorem cell463_check :
    cell463.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 30, 6] witnessGeometryChecked (by decide))
      cell463_check_indexed

/-- Closed-cover cell 464 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 30, 6]`; `cell464_check` verifies
its explicit-potential certificate. -/
def cell464 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell464_check_hints : cell464.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell464_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell464_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell464_check_hints

theorem cell464_check :
    cell464.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 30, 6] witnessGeometryChecked (by decide))
      cell464_check_indexed

/-- Closed-cover cell 465 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 30, 6]`; `cell465_check` verifies
its explicit-potential certificate. -/
def cell465 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell465_check_hints : cell465.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell465_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell465_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell465_check_hints

theorem cell465_check :
    cell465.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 30, 6] witnessGeometryChecked (by decide))
      cell465_check_indexed

/-- Closed-cover cell 466 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 30, 6]`; `cell466_check` verifies
its explicit-potential certificate. -/
def cell466 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell466_check_hints : cell466.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell466_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell466_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell466_check_hints

theorem cell466_check :
    cell466.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 30, 6] witnessGeometryChecked (by decide))
      cell466_check_indexed

/-- Closed-cover cell 467 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 27, 6]`; `cell467_check` verifies
its explicit-potential certificate. -/
def cell467 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell467_check_hints : cell467.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell467_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell467_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell467_check_hints

theorem cell467_check :
    cell467.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 27, 6] witnessGeometryChecked (by decide))
      cell467_check_indexed

/-- Closed-cover cell 468 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 28, 6]`; `cell468_check` verifies
its explicit-potential certificate. -/
def cell468 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell468_check_hints : cell468.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell468_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell468_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell468_check_hints

theorem cell468_check :
    cell468.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 28, 6] witnessGeometryChecked (by decide))
      cell468_check_indexed

/-- Closed-cover cell 469 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 29, 6]`; `cell469_check` verifies
its explicit-potential certificate. -/
def cell469 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell469_check_hints : cell469.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell469_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell469_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell469_check_hints

theorem cell469_check :
    cell469.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 29, 6] witnessGeometryChecked (by decide))
      cell469_check_indexed

/-- Closed-cover cell 470 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 30, 6]`; `cell470_check` verifies
its explicit-potential certificate. -/
def cell470 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell470_check_hints : cell470.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 21, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 5, 22]] = true := by
  decide +kernel

private theorem cell470_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell470_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell470_check_hints

theorem cell470_check :
    cell470.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 30, 6] witnessGeometryChecked (by decide))
      cell470_check_indexed

/-- Closed-cover cell 471 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 27, 6]`; `cell471_check` verifies
its explicit-potential certificate. -/
def cell471 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell471_check_hints : cell471.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell471_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell471_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell471_check_hints

theorem cell471_check :
    cell471.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 27, 6] witnessGeometryChecked (by decide))
      cell471_check_indexed

/-- Closed-cover cell 472 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 28, 6]`; `cell472_check` verifies
its explicit-potential certificate. -/
def cell472 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell472_check_hints : cell472.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell472_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell472_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell472_check_hints

theorem cell472_check :
    cell472.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 28, 6] witnessGeometryChecked (by decide))
      cell472_check_indexed

/-- Closed-cover cell 473 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 29, 6]`; `cell473_check` verifies
its explicit-potential certificate. -/
def cell473 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell473_check_hints : cell473.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell473_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell473_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell473_check_hints

theorem cell473_check :
    cell473.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 29, 6] witnessGeometryChecked (by decide))
      cell473_check_indexed

/-- Closed-cover cell 474 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 30, 6]`; `cell474_check` verifies
its explicit-potential certificate. -/
def cell474 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell474_check_hints : cell474.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell474_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell474_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell474_check_hints

theorem cell474_check :
    cell474.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 30, 6] witnessGeometryChecked (by decide))
      cell474_check_indexed

/-- Closed-cover cell 475 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 27, 6]`; `cell475_check` verifies
its explicit-potential certificate. -/
def cell475 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell475_check_hints : cell475.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell475_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell475_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell475_check_hints

theorem cell475_check :
    cell475.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 27, 6] witnessGeometryChecked (by decide))
      cell475_check_indexed

/-- Closed-cover cell 476 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 28, 6]`; `cell476_check` verifies
its explicit-potential certificate. -/
def cell476 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell476_check_hints : cell476.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell476_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell476_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell476_check_hints

theorem cell476_check :
    cell476.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 28, 6] witnessGeometryChecked (by decide))
      cell476_check_indexed

/-- Closed-cover cell 477 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 29, 6]`; `cell477_check` verifies
its explicit-potential certificate. -/
def cell477 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell477_check_hints : cell477.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell477_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell477_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell477_check_hints

theorem cell477_check :
    cell477.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 29, 6] witnessGeometryChecked (by decide))
      cell477_check_indexed

/-- Closed-cover cell 478 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 30, 6]`; `cell478_check` verifies
its explicit-potential certificate. -/
def cell478 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell478_check_hints : cell478.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell478_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell478_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell478_check_hints

theorem cell478_check :
    cell478.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 30, 6] witnessGeometryChecked (by decide))
      cell478_check_indexed

/-- Closed-cover cell 479 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 27, 6]`; `cell479_check` verifies
its explicit-potential certificate. -/
def cell479 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell479_check_hints : cell479.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell479_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell479_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell479_check_hints

theorem cell479_check :
    cell479.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 27, 6] witnessGeometryChecked (by decide))
      cell479_check_indexed

/-- Closed-cover cell 480 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 28, 6]`; `cell480_check` verifies
its explicit-potential certificate. -/
def cell480 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell480_check_hints : cell480.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell480_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell480_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell480_check_hints

theorem cell480_check :
    cell480.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 28, 6] witnessGeometryChecked (by decide))
      cell480_check_indexed

/-- Closed-cover cell 481 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 29, 6]`; `cell481_check` verifies
its explicit-potential certificate. -/
def cell481 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell481_check_hints : cell481.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell481_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell481_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell481_check_hints

theorem cell481_check :
    cell481.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 29, 6] witnessGeometryChecked (by decide))
      cell481_check_indexed

/-- Closed-cover cell 482 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 30, 6]`; `cell482_check` verifies
its explicit-potential certificate. -/
def cell482 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell482_check_hints : cell482.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 23, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 5, 24]] = true := by
  decide +kernel

private theorem cell482_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell482_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell482_check_hints

theorem cell482_check :
    cell482.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 30, 6] witnessGeometryChecked (by decide))
      cell482_check_indexed

/-- The ordered row-06 closed-cover cell block with global indices 387 through 482, used when
assembling the full 483-cell cover. -/
def chunk : List (CoordinateCell row06Core) :=
  [cell387, cell388, cell389, cell390, cell391, cell392, cell393, cell394, cell395, cell396,
  cell397, cell398, cell399, cell400, cell401, cell402, cell403, cell404, cell405, cell406, cell407,
  cell408, cell409, cell410, cell411, cell412, cell413, cell414, cell415, cell416, cell417, cell418,
  cell419, cell420, cell421, cell422, cell423, cell424, cell425, cell426, cell427, cell428, cell429,
  cell430, cell431, cell432, cell433, cell434, cell435, cell436, cell437, cell438, cell439, cell440,
  cell441, cell442, cell443, cell444, cell445, cell446, cell447, cell448, cell449, cell450, cell451,
  cell452, cell453, cell454, cell455, cell456, cell457, cell458, cell459, cell460, cell461, cell462,
  cell463, cell464, cell465, cell466, cell467, cell468, cell469, cell470, cell471, cell472, cell473,
  cell474, cell475, cell476, cell477, cell478, cell479, cell480, cell481, cell482]

theorem chunk_check :
    chunk.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [chunk, cell387_check, cell388_check, cell389_check, cell390_check, cell391_check,
    cell392_check, cell393_check, cell394_check, cell395_check, cell396_check, cell397_check,
    cell398_check, cell399_check, cell400_check, cell401_check, cell402_check, cell403_check,
    cell404_check, cell405_check, cell406_check, cell407_check, cell408_check, cell409_check,
    cell410_check, cell411_check, cell412_check, cell413_check, cell414_check, cell415_check,
    cell416_check, cell417_check, cell418_check, cell419_check, cell420_check, cell421_check,
    cell422_check, cell423_check, cell424_check, cell425_check, cell426_check, cell427_check,
    cell428_check, cell429_check, cell430_check, cell431_check, cell432_check, cell433_check,
    cell434_check, cell435_check, cell436_check, cell437_check, cell438_check, cell439_check,
    cell440_check, cell441_check, cell442_check, cell443_check, cell444_check, cell445_check,
    cell446_check, cell447_check, cell448_check, cell449_check, cell450_check, cell451_check,
    cell452_check, cell453_check, cell454_check, cell455_check, cell456_check, cell457_check,
    cell458_check, cell459_check, cell460_check, cell461_check, cell462_check, cell463_check,
    cell464_check, cell465_check, cell466_check, cell467_check, cell468_check, cell469_check,
    cell470_check, cell471_check, cell472_check, cell473_check, cell474_check, cell475_check,
    cell476_check, cell477_check, cell478_check, cell479_check, cell480_check, cell481_check,
    cell482_check]

end AtanasovRanganathan.GenusFiveRow06CoverCells4
