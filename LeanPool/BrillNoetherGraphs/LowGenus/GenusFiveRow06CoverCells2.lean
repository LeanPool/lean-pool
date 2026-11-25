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

Generated cell chunk 2 of 5 for the AR row-06 chamber cover
(cells 194-290).  Split across modules because the kernel cost of
replaying a cell is cumulative within one Lean process. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06CoverCells2

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow06CoverBase

/-- Closed-cover cell 194 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 26, 4, 5, 16]`; `cell194_check` verifies
its explicit-potential certificate. -/
def cell194 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 26, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

attribute [local instance 2000] CertificateData.decidableCheckClosedRowsKernel

private theorem cell194_check_hints : cell194.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell194_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell194_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell194_check_hints

theorem cell194_check :
    cell194.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 26, 4, 5, 16] witnessGeometryChecked (by decide))
      cell194_check_indexed

/-- Closed-cover cell 195 for the fixed row-06 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 5, 12]`; `cell195_check` verifies
its explicit-potential certificate. -/
def cell195 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell195_check_hints : cell195.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 19]] = true := by
  decide +kernel

private theorem cell195_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell195_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell195_check_hints

theorem cell195_check :
    cell195.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 5, 12] witnessGeometryChecked (by decide))
      cell195_check_indexed

/-- Closed-cover cell 196 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 5, 12]`; `cell196_check` verifies
its explicit-potential certificate. -/
def cell196 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell196_check_hints : cell196.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 18]] = true := by
  decide +kernel

private theorem cell196_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell196_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell196_check_hints

theorem cell196_check :
    cell196.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 5, 12] witnessGeometryChecked (by decide))
      cell196_check_indexed

/-- Closed-cover cell 197 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 5, 12]`; `cell197_check` verifies
its explicit-potential certificate. -/
def cell197 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell197_check_hints : cell197.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell197_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell197_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell197_check_hints

theorem cell197_check :
    cell197.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 5, 12] witnessGeometryChecked (by decide))
      cell197_check_indexed

/-- Closed-cover cell 198 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 5, 12]`; `cell198_check` verifies
its explicit-potential certificate. -/
def cell198 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell198_check_hints : cell198.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell198_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell198_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell198_check_hints

theorem cell198_check :
    cell198.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 5, 12] witnessGeometryChecked (by decide))
      cell198_check_indexed

/-- Closed-cover cell 199 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 5, 12]`; `cell199_check` verifies
its explicit-potential certificate. -/
def cell199 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell199_check_hints : cell199.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]] = true := by
  decide +kernel

private theorem cell199_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell199_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell199_check_hints

theorem cell199_check :
    cell199.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 5, 12] witnessGeometryChecked (by decide))
      cell199_check_indexed

/-- Closed-cover cell 200 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 5, 13]`; `cell200_check` verifies
its explicit-potential certificate. -/
def cell200 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell200_check_hints : cell200.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 0, 0, 6, 21]] = true := by
  decide +kernel

private theorem cell200_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell200_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell200_check_hints

theorem cell200_check :
    cell200.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 5, 13] witnessGeometryChecked (by decide))
      cell200_check_indexed

/-- Closed-cover cell 201 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 5, 13]`; `cell201_check` verifies
its explicit-potential certificate. -/
def cell201 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell201_check_hints : cell201.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 6, 20]] = true := by
  decide +kernel

private theorem cell201_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell201_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell201_check_hints

theorem cell201_check :
    cell201.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 5, 13] witnessGeometryChecked (by decide))
      cell201_check_indexed

/-- Closed-cover cell 202 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 5, 13]`; `cell202_check` verifies
its explicit-potential certificate. -/
def cell202 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell202_check_hints : cell202.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]] = true := by
  decide +kernel

private theorem cell202_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell202_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell202_check_hints

theorem cell202_check :
    cell202.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 5, 13] witnessGeometryChecked (by decide))
      cell202_check_indexed

/-- Closed-cover cell 203 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 5, 13]`; `cell203_check` verifies
its explicit-potential certificate. -/
def cell203 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell203_check_hints : cell203.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]] = true := by
  decide +kernel

private theorem cell203_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell203_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell203_check_hints

theorem cell203_check :
    cell203.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 5, 13] witnessGeometryChecked (by decide))
      cell203_check_indexed

/-- Closed-cover cell 204 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 5, 13]`; `cell204_check` verifies
its explicit-potential certificate. -/
def cell204 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell204_check_hints : cell204.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]] = true := by
  decide +kernel

private theorem cell204_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell204_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell204_check_hints

theorem cell204_check :
    cell204.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 5, 13] witnessGeometryChecked (by decide))
      cell204_check_indexed

/-- Closed-cover cell 205 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 5, 14]`; `cell205_check` verifies
its explicit-potential certificate. -/
def cell205 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell205_check_hints : cell205.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 0, 0, 6, 21]] = true := by
  decide +kernel

private theorem cell205_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell205_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell205_check_hints

theorem cell205_check :
    cell205.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 5, 14] witnessGeometryChecked (by decide))
      cell205_check_indexed

/-- Closed-cover cell 206 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 5, 14]`; `cell206_check` verifies
its explicit-potential certificate. -/
def cell206 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell206_check_hints : cell206.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 6, 20]] = true := by
  decide +kernel

private theorem cell206_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell206_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell206_check_hints

theorem cell206_check :
    cell206.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 5, 14] witnessGeometryChecked (by decide))
      cell206_check_indexed

/-- Closed-cover cell 207 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 5, 14]`; `cell207_check` verifies
its explicit-potential certificate. -/
def cell207 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell207_check_hints : cell207.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]] = true := by
  decide +kernel

private theorem cell207_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell207_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell207_check_hints

theorem cell207_check :
    cell207.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 5, 14] witnessGeometryChecked (by decide))
      cell207_check_indexed

/-- Closed-cover cell 208 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 5, 14]`; `cell208_check` verifies
its explicit-potential certificate. -/
def cell208 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell208_check_hints : cell208.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]] = true := by
  decide +kernel

private theorem cell208_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell208_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell208_check_hints

theorem cell208_check :
    cell208.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 5, 14] witnessGeometryChecked (by decide))
      cell208_check_indexed

/-- Closed-cover cell 209 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 5, 14]`; `cell209_check` verifies
its explicit-potential certificate. -/
def cell209 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell209_check_hints : cell209.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]] = true := by
  decide +kernel

private theorem cell209_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell209_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell209_check_hints

theorem cell209_check :
    cell209.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 5, 14] witnessGeometryChecked (by decide))
      cell209_check_indexed

/-- Closed-cover cell 210 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 22, 4, 5, 16]`; `cell210_check` verifies
its explicit-potential certificate. -/
def cell210 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 22, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell210_check_hints : cell210.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 19, 21]] = true := by
  decide +kernel

private theorem cell210_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell210_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell210_check_hints

theorem cell210_check :
    cell210.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 22, 4, 5, 16] witnessGeometryChecked (by decide))
      cell210_check_indexed

/-- Closed-cover cell 211 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 22, 4, 5, 16]`; `cell211_check` verifies
its explicit-potential certificate. -/
def cell211 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 22, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell211_check_hints : cell211.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 18, 20]] = true := by
  decide +kernel

private theorem cell211_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell211_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell211_check_hints

theorem cell211_check :
    cell211.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 22, 4, 5, 16] witnessGeometryChecked (by decide))
      cell211_check_indexed

/-- Closed-cover cell 212 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 22, 4, 5, 16]`; `cell212_check` verifies
its explicit-potential certificate. -/
def cell212 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 22, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell212_check_hints : cell212.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]] = true := by
  decide +kernel

private theorem cell212_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell212_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell212_check_hints

theorem cell212_check :
    cell212.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 22, 4, 5, 16] witnessGeometryChecked (by decide))
      cell212_check_indexed

/-- Closed-cover cell 213 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 22, 4, 5, 16]`; `cell213_check` verifies
its explicit-potential certificate. -/
def cell213 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 22, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell213_check_hints : cell213.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]] = true := by
  decide +kernel

private theorem cell213_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell213_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell213_check_hints

theorem cell213_check :
    cell213.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 22, 4, 5, 16] witnessGeometryChecked (by decide))
      cell213_check_indexed

/-- Closed-cover cell 214 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 22, 4, 5, 16]`; `cell214_check` verifies
its explicit-potential certificate. -/
def cell214 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 22, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell214_check_hints : cell214.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]] = true := by
  decide +kernel

private theorem cell214_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell214_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell214_check_hints

theorem cell214_check :
    cell214.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 22, 4, 5, 16] witnessGeometryChecked (by decide))
      cell214_check_indexed

/-- Closed-cover cell 215 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 5, 12]`; `cell215_check` verifies
its explicit-potential certificate. -/
def cell215 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell215_check_hints : cell215.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell215_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell215_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell215_check_hints

theorem cell215_check :
    cell215.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 5, 12] witnessGeometryChecked (by decide))
      cell215_check_indexed

/-- Closed-cover cell 216 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 5, 12]`; `cell216_check` verifies
its explicit-potential certificate. -/
def cell216 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell216_check_hints : cell216.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell216_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell216_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell216_check_hints

theorem cell216_check :
    cell216.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 5, 12] witnessGeometryChecked (by decide))
      cell216_check_indexed

/-- Closed-cover cell 217 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 5, 12]`; `cell217_check` verifies
its explicit-potential certificate. -/
def cell217 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell217_check_hints : cell217.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell217_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell217_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell217_check_hints

theorem cell217_check :
    cell217.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 5, 12] witnessGeometryChecked (by decide))
      cell217_check_indexed

/-- Closed-cover cell 218 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 5, 12]`; `cell218_check` verifies
its explicit-potential certificate. -/
def cell218 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell218_check_hints : cell218.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell218_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell218_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell218_check_hints

theorem cell218_check :
    cell218.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 5, 12] witnessGeometryChecked (by decide))
      cell218_check_indexed

/-- Closed-cover cell 219 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 5, 12]`; `cell219_check` verifies
its explicit-potential certificate. -/
def cell219 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell219_check_hints : cell219.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell219_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell219_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell219_check_hints

theorem cell219_check :
    cell219.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 5, 12] witnessGeometryChecked (by decide))
      cell219_check_indexed

/-- Closed-cover cell 220 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 5, 13]`; `cell220_check` verifies
its explicit-potential certificate. -/
def cell220 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell220_check_hints : cell220.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 0, 0, 6, 23]]
     = true := by
  decide +kernel

private theorem cell220_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell220_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell220_check_hints

theorem cell220_check :
    cell220.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 5, 13] witnessGeometryChecked (by decide))
      cell220_check_indexed

/-- Closed-cover cell 221 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 5, 13]`; `cell221_check` verifies
its explicit-potential certificate. -/
def cell221 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell221_check_hints : cell221.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell221_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell221_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell221_check_hints

theorem cell221_check :
    cell221.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 5, 13] witnessGeometryChecked (by decide))
      cell221_check_indexed

/-- Closed-cover cell 222 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 5, 13]`; `cell222_check` verifies
its explicit-potential certificate. -/
def cell222 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell222_check_hints : cell222.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell222_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell222_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell222_check_hints

theorem cell222_check :
    cell222.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 5, 13] witnessGeometryChecked (by decide))
      cell222_check_indexed

/-- Closed-cover cell 223 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 5, 13]`; `cell223_check` verifies
its explicit-potential certificate. -/
def cell223 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell223_check_hints : cell223.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell223_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell223_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell223_check_hints

theorem cell223_check :
    cell223.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 5, 13] witnessGeometryChecked (by decide))
      cell223_check_indexed

/-- Closed-cover cell 224 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 5, 13]`; `cell224_check` verifies
its explicit-potential certificate. -/
def cell224 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell224_check_hints : cell224.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell224_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell224_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell224_check_hints

theorem cell224_check :
    cell224.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 5, 13] witnessGeometryChecked (by decide))
      cell224_check_indexed

/-- Closed-cover cell 225 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 5, 14]`; `cell225_check` verifies
its explicit-potential certificate. -/
def cell225 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell225_check_hints : cell225.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 0, 0, 6, 23]]
     = true := by
  decide +kernel

private theorem cell225_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell225_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell225_check_hints

theorem cell225_check :
    cell225.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 5, 14] witnessGeometryChecked (by decide))
      cell225_check_indexed

/-- Closed-cover cell 226 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 5, 14]`; `cell226_check` verifies
its explicit-potential certificate. -/
def cell226 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell226_check_hints : cell226.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell226_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell226_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell226_check_hints

theorem cell226_check :
    cell226.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 5, 14] witnessGeometryChecked (by decide))
      cell226_check_indexed

/-- Closed-cover cell 227 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 5, 14]`; `cell227_check` verifies
its explicit-potential certificate. -/
def cell227 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell227_check_hints : cell227.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell227_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell227_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell227_check_hints

theorem cell227_check :
    cell227.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 5, 14] witnessGeometryChecked (by decide))
      cell227_check_indexed

/-- Closed-cover cell 228 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 5, 14]`; `cell228_check` verifies
its explicit-potential certificate. -/
def cell228 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell228_check_hints : cell228.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell228_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell228_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell228_check_hints

theorem cell228_check :
    cell228.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 5, 14] witnessGeometryChecked (by decide))
      cell228_check_indexed

/-- Closed-cover cell 229 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 5, 14]`; `cell229_check` verifies
its explicit-potential certificate. -/
def cell229 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell229_check_hints : cell229.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell229_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell229_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell229_check_hints

theorem cell229_check :
    cell229.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 5, 14] witnessGeometryChecked (by decide))
      cell229_check_indexed

/-- Closed-cover cell 230 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 23, 4, 5, 16]`; `cell230_check` verifies
its explicit-potential certificate. -/
def cell230 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 23, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell230_check_hints : cell230.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 21, 23]]
     = true := by
  decide +kernel

private theorem cell230_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell230_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell230_check_hints

theorem cell230_check :
    cell230.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 23, 4, 5, 16] witnessGeometryChecked (by decide))
      cell230_check_indexed

/-- Closed-cover cell 231 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 23, 4, 5, 16]`; `cell231_check` verifies
its explicit-potential certificate. -/
def cell231 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 23, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell231_check_hints : cell231.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell231_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell231_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell231_check_hints

theorem cell231_check :
    cell231.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 23, 4, 5, 16] witnessGeometryChecked (by decide))
      cell231_check_indexed

/-- Closed-cover cell 232 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 23, 4, 5, 16]`; `cell232_check` verifies
its explicit-potential certificate. -/
def cell232 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 23, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell232_check_hints : cell232.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23,
     22, 24]] = true := by
  decide +kernel

private theorem cell232_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell232_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell232_check_hints

theorem cell232_check :
    cell232.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 23, 4, 5, 16] witnessGeometryChecked (by decide))
      cell232_check_indexed

/-- Closed-cover cell 233 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 23, 4, 5, 16]`; `cell233_check` verifies
its explicit-potential certificate. -/
def cell233 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 23, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell233_check_hints : cell233.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23,
     22, 24]] = true := by
  decide +kernel

private theorem cell233_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell233_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell233_check_hints

theorem cell233_check :
    cell233.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 23, 4, 5, 16] witnessGeometryChecked (by decide))
      cell233_check_indexed

/-- Closed-cover cell 234 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 23, 4, 5, 16]`; `cell234_check` verifies
its explicit-potential certificate. -/
def cell234 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 23, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell234_check_hints : cell234.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22, 24]]
     = true := by
  decide +kernel

private theorem cell234_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell234_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell234_check_hints

theorem cell234_check :
    cell234.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 23, 4, 5, 16] witnessGeometryChecked (by decide))
      cell234_check_indexed

/-- Closed-cover cell 235 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 24, 4, 5, 12]`; `cell235_check` verifies
its explicit-potential certificate. -/
def cell235 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 24, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell235_check_hints : cell235.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell235_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell235_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell235_check_hints

theorem cell235_check :
    cell235.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 24, 4, 5, 12] witnessGeometryChecked (by decide))
      cell235_check_indexed

/-- Closed-cover cell 236 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 5, 12]`; `cell236_check` verifies
its explicit-potential certificate. -/
def cell236 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell236_check_hints : cell236.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell236_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell236_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell236_check_hints

theorem cell236_check :
    cell236.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 5, 12] witnessGeometryChecked (by decide))
      cell236_check_indexed

/-- Closed-cover cell 237 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 5, 12]`; `cell237_check` verifies
its explicit-potential certificate. -/
def cell237 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell237_check_hints : cell237.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell237_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell237_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell237_check_hints

theorem cell237_check :
    cell237.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 5, 12] witnessGeometryChecked (by decide))
      cell237_check_indexed

/-- Closed-cover cell 238 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 5, 12]`; `cell238_check` verifies
its explicit-potential certificate. -/
def cell238 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell238_check_hints : cell238.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell238_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell238_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell238_check_hints

theorem cell238_check :
    cell238.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 5, 12] witnessGeometryChecked (by decide))
      cell238_check_indexed

/-- Closed-cover cell 239 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 5, 12]`; `cell239_check` verifies
its explicit-potential certificate. -/
def cell239 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell239_check_hints : cell239.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell239_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell239_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell239_check_hints

theorem cell239_check :
    cell239.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 5, 12] witnessGeometryChecked (by decide))
      cell239_check_indexed

/-- Closed-cover cell 240 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 24, 4, 5, 13]`; `cell240_check` verifies
its explicit-potential certificate. -/
def cell240 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 24, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell240_check_hints : cell240.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 0, 0, 6, 23]]
     = true := by
  decide +kernel

private theorem cell240_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell240_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell240_check_hints

theorem cell240_check :
    cell240.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 24, 4, 5, 13] witnessGeometryChecked (by decide))
      cell240_check_indexed

/-- Closed-cover cell 241 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 5, 13]`; `cell241_check` verifies
its explicit-potential certificate. -/
def cell241 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell241_check_hints : cell241.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell241_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell241_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell241_check_hints

theorem cell241_check :
    cell241.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 5, 13] witnessGeometryChecked (by decide))
      cell241_check_indexed

/-- Closed-cover cell 242 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 5, 13]`; `cell242_check` verifies
its explicit-potential certificate. -/
def cell242 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell242_check_hints : cell242.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell242_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell242_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell242_check_hints

theorem cell242_check :
    cell242.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 5, 13] witnessGeometryChecked (by decide))
      cell242_check_indexed

/-- Closed-cover cell 243 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 5, 13]`; `cell243_check` verifies
its explicit-potential certificate. -/
def cell243 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell243_check_hints : cell243.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell243_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell243_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell243_check_hints

theorem cell243_check :
    cell243.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 5, 13] witnessGeometryChecked (by decide))
      cell243_check_indexed

/-- Closed-cover cell 244 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 5, 13]`; `cell244_check` verifies
its explicit-potential certificate. -/
def cell244 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell244_check_hints : cell244.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell244_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell244_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell244_check_hints

theorem cell244_check :
    cell244.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 5, 13] witnessGeometryChecked (by decide))
      cell244_check_indexed

/-- Closed-cover cell 245 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 24, 4, 5, 14]`; `cell245_check` verifies
its explicit-potential certificate. -/
def cell245 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 24, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell245_check_hints : cell245.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 11, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 0, 0, 6, 23]]
     = true := by
  decide +kernel

private theorem cell245_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell245_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell245_check_hints

theorem cell245_check :
    cell245.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 24, 4, 5, 14] witnessGeometryChecked (by decide))
      cell245_check_indexed

/-- Closed-cover cell 246 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 5, 14]`; `cell246_check` verifies
its explicit-potential certificate. -/
def cell246 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell246_check_hints : cell246.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell246_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell246_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell246_check_hints

theorem cell246_check :
    cell246.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 5, 14] witnessGeometryChecked (by decide))
      cell246_check_indexed

/-- Closed-cover cell 247 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 5, 14]`; `cell247_check` verifies
its explicit-potential certificate. -/
def cell247 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell247_check_hints : cell247.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell247_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell247_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell247_check_hints

theorem cell247_check :
    cell247.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 5, 14] witnessGeometryChecked (by decide))
      cell247_check_indexed

/-- Closed-cover cell 248 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 5, 14]`; `cell248_check` verifies
its explicit-potential certificate. -/
def cell248 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell248_check_hints : cell248.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell248_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell248_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell248_check_hints

theorem cell248_check :
    cell248.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 5, 14] witnessGeometryChecked (by decide))
      cell248_check_indexed

/-- Closed-cover cell 249 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 5, 14]`; `cell249_check` verifies
its explicit-potential certificate. -/
def cell249 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell249_check_hints : cell249.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell249_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell249_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell249_check_hints

theorem cell249_check :
    cell249.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 5, 14] witnessGeometryChecked (by decide))
      cell249_check_indexed

/-- Closed-cover cell 250 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 24, 4, 5, 16]`; `cell250_check` verifies
its explicit-potential certificate. -/
def cell250 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 24, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell250_check_hints : cell250.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 15, 16, 0, 0, 11, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell250_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell250_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell250_check_hints

theorem cell250_check :
    cell250.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 24, 4, 5, 16] witnessGeometryChecked (by decide))
      cell250_check_indexed

/-- Closed-cover cell 251 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 24, 4, 5, 16]`; `cell251_check` verifies
its explicit-potential certificate. -/
def cell251 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 24, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell251_check_hints : cell251.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23,
     22, 24]] = true := by
  decide +kernel

private theorem cell251_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell251_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell251_check_hints

theorem cell251_check :
    cell251.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 24, 4, 5, 16] witnessGeometryChecked (by decide))
      cell251_check_indexed

/-- Closed-cover cell 252 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 24, 4, 5, 16]`; `cell252_check` verifies
its explicit-potential certificate. -/
def cell252 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 24, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell252_check_hints : cell252.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23,
     22, 24]] = true := by
  decide +kernel

private theorem cell252_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell252_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell252_check_hints

theorem cell252_check :
    cell252.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 24, 4, 5, 16] witnessGeometryChecked (by decide))
      cell252_check_indexed

/-- Closed-cover cell 253 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 5, 16]`; `cell253_check` verifies
its explicit-potential certificate. -/
def cell253 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell253_check_hints : cell253.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 18, 0, 0, 11, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22, 24]]
     = true := by
  decide +kernel

private theorem cell253_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell253_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell253_check_hints

theorem cell253_check :
    cell253.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 24, 4, 5, 16] witnessGeometryChecked (by decide))
      cell253_check_indexed

/-- Closed-cover cell 254 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 26, 4, 5, 12]`; `cell254_check` verifies
its explicit-potential certificate. -/
def cell254 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 26, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell254_check_hints : cell254.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 16, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     21]] = true := by
  decide +kernel

private theorem cell254_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell254_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell254_check_hints

theorem cell254_check :
    cell254.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 26, 4, 5, 12] witnessGeometryChecked (by decide))
      cell254_check_indexed

/-- Closed-cover cell 255 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 5, 12]`; `cell255_check` verifies
its explicit-potential certificate. -/
def cell255 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell255_check_hints : cell255.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     20]] = true := by
  decide +kernel

private theorem cell255_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell255_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell255_check_hints

theorem cell255_check :
    cell255.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 5, 12] witnessGeometryChecked (by decide))
      cell255_check_indexed

/-- Closed-cover cell 256 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 5, 12]`; `cell256_check` verifies
its explicit-potential certificate. -/
def cell256 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell256_check_hints : cell256.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell256_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell256_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell256_check_hints

theorem cell256_check :
    cell256.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 5, 12] witnessGeometryChecked (by decide))
      cell256_check_indexed

/-- Closed-cover cell 257 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 5, 12]`; `cell257_check` verifies
its explicit-potential certificate. -/
def cell257 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell257_check_hints : cell257.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell257_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell257_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell257_check_hints

theorem cell257_check :
    cell257.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 5, 12] witnessGeometryChecked (by decide))
      cell257_check_indexed

/-- Closed-cover cell 258 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 5, 12]`; `cell258_check` verifies
its explicit-potential certificate. -/
def cell258 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 5, 12] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]] }

private theorem cell258_check_hints : cell258.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell258_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell258_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell258_check_hints

theorem cell258_check :
    cell258.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 5, 12] witnessGeometryChecked (by decide))
      cell258_check_indexed

/-- Closed-cover cell 259 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 26, 4, 5, 13]`; `cell259_check` verifies
its explicit-potential certificate. -/
def cell259 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 26, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell259_check_hints : cell259.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 16, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 9], [0, 0, 0, 0, 0, 0, 0, 0, 20, 8], [0, 0, 0, 0, 0, 0, 0, 0, 21, 22, 0, 0, 6, 23]]
     = true := by
  decide +kernel

private theorem cell259_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell259_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell259_check_hints

theorem cell259_check :
    cell259.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 26, 4, 5, 13] witnessGeometryChecked (by decide))
      cell259_check_indexed

/-- Closed-cover cell 260 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 5, 13]`; `cell260_check` verifies
its explicit-potential certificate. -/
def cell260 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell260_check_hints : cell260.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell260_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell260_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell260_check_hints

theorem cell260_check :
    cell260.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 5, 13] witnessGeometryChecked (by decide))
      cell260_check_indexed

/-- Closed-cover cell 261 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 5, 13]`; `cell261_check` verifies
its explicit-potential certificate. -/
def cell261 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell261_check_hints : cell261.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell261_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell261_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell261_check_hints

theorem cell261_check :
    cell261.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 5, 13] witnessGeometryChecked (by decide))
      cell261_check_indexed

/-- Closed-cover cell 262 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 5, 13]`; `cell262_check` verifies
its explicit-potential certificate. -/
def cell262 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell262_check_hints : cell262.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell262_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell262_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell262_check_hints

theorem cell262_check :
    cell262.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 5, 13] witnessGeometryChecked (by decide))
      cell262_check_indexed

/-- Closed-cover cell 263 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 5, 13]`; `cell263_check` verifies
its explicit-potential certificate. -/
def cell263 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 5, 13] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell263_check_hints : cell263.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell263_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell263_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell263_check_hints

theorem cell263_check :
    cell263.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 5, 13] witnessGeometryChecked (by decide))
      cell263_check_indexed

/-- Closed-cover cell 264 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 5, 14]`; `cell264_check` verifies
its explicit-potential certificate. -/
def cell264 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell264_check_hints : cell264.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 6, 22]]
     = true := by
  decide +kernel

private theorem cell264_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell264_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell264_check_hints

theorem cell264_check :
    cell264.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 5, 14] witnessGeometryChecked (by decide))
      cell264_check_indexed

/-- Closed-cover cell 265 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 26, 4, 5, 16]`; `cell265_check` verifies
its explicit-potential certificate. -/
def cell265 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 26, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell265_check_hints : cell265.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 15, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 18, 9], [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 20, 22]]
     = true := by
  decide +kernel

private theorem cell265_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell265_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell265_check_hints

theorem cell265_check :
    cell265.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 26, 4, 5, 16] witnessGeometryChecked (by decide))
      cell265_check_indexed

/-- Closed-cover cell 266 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 5, 14]`; `cell266_check` verifies
its explicit-potential certificate. -/
def cell266 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell266_check_hints : cell266.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell266_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell266_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell266_check_hints

theorem cell266_check :
    cell266.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 5, 14] witnessGeometryChecked (by decide))
      cell266_check_indexed

/-- Closed-cover cell 267 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 26, 4, 5, 16]`; `cell267_check` verifies
its explicit-potential certificate. -/
def cell267 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 26, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell267_check_hints : cell267.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23,
     22, 24]] = true := by
  decide +kernel

private theorem cell267_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell267_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell267_check_hints

theorem cell267_check :
    cell267.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 26, 4, 5, 16] witnessGeometryChecked (by decide))
      cell267_check_indexed

/-- Closed-cover cell 268 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 5, 14]`; `cell268_check` verifies
its explicit-potential certificate. -/
def cell268 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell268_check_hints : cell268.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0,
     6, 24]] = true := by
  decide +kernel

private theorem cell268_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell268_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell268_check_hints

theorem cell268_check :
    cell268.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 5, 14] witnessGeometryChecked (by decide))
      cell268_check_indexed

/-- Closed-cover cell 269 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 26, 4, 5, 16]`; `cell269_check` verifies
its explicit-potential certificate. -/
def cell269 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 26, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell269_check_hints : cell269.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23,
     22, 24]] = true := by
  decide +kernel

private theorem cell269_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell269_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell269_check_hints

theorem cell269_check :
    cell269.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 26, 4, 5, 16] witnessGeometryChecked (by decide))
      cell269_check_indexed

/-- Closed-cover cell 270 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 5, 14]`; `cell270_check` verifies
its explicit-potential certificate. -/
def cell270 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 5, 14] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0]] }

private theorem cell270_check_hints : cell270.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 6, 24]]
     = true := by
  decide +kernel

private theorem cell270_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell270_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell270_check_hints

theorem cell270_check :
    cell270.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 5, 14] witnessGeometryChecked (by decide))
      cell270_check_indexed

/-- Closed-cover cell 271 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 26, 4, 5, 16]`; `cell271_check` verifies
its explicit-potential certificate. -/
def cell271 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 26, 4, 5, 16] : List Nat).getD anchor.val 0) defaultWitness
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
      aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0]] }

private theorem cell271_check_hints : cell271.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 17, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 9], [0, 0, 0, 0, 0, 0, 0, 0, 21, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 22, 24]]
     = true := by
  decide +kernel

private theorem cell271_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell271_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell271_check_hints

theorem cell271_check :
    cell271.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 26, 4, 5, 16] witnessGeometryChecked (by decide))
      cell271_check_indexed

/-- Closed-cover cell 272 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 4, 27, 6]`; `cell272_check` verifies its
explicit-potential certificate. -/
def cell272 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell272_check_hints : cell272.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 18]] = true := by
  decide +kernel

private theorem cell272_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell272_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell272_check_hints

theorem cell272_check :
    cell272.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 3, 4, 27, 6] witnessGeometryChecked (by decide))
      cell272_check_indexed

/-- Closed-cover cell 273 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 4, 28, 6]`; `cell273_check` verifies its
explicit-potential certificate. -/
def cell273 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell273_check_hints : cell273.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell273_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell273_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell273_check_hints

theorem cell273_check :
    cell273.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 3, 4, 28, 6] witnessGeometryChecked (by decide))
      cell273_check_indexed

/-- Closed-cover cell 274 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 4, 29, 6]`; `cell274_check` verifies its
explicit-potential certificate. -/
def cell274 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell274_check_hints : cell274.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell274_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell274_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell274_check_hints

theorem cell274_check :
    cell274.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 3, 4, 29, 6] witnessGeometryChecked (by decide))
      cell274_check_indexed

/-- Closed-cover cell 275 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 4, 30, 6]`; `cell275_check` verifies its
explicit-potential certificate. -/
def cell275 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell275_check_hints : cell275.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell275_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell275_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell275_check_hints

theorem cell275_check :
    cell275.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 1, 2, 2, 3, 4, 30, 6] witnessGeometryChecked (by decide))
      cell275_check_indexed

/-- Closed-cover cell 276 for the fixed row-06 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 4, 27, 6]`; `cell276_check` verifies its
explicit-potential certificate. -/
def cell276 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell276_check_hints : cell276.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 18, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 19]] = true := by
  decide +kernel

private theorem cell276_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell276_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell276_check_hints

theorem cell276_check :
    cell276.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 3, 4, 27, 6] witnessGeometryChecked (by decide))
      cell276_check_indexed

/-- Closed-cover cell 277 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 4, 27, 6]`; `cell277_check` verifies its
explicit-potential certificate. -/
def cell277 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell277_check_hints : cell277.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 17, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 18]] = true := by
  decide +kernel

private theorem cell277_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell277_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell277_check_hints

theorem cell277_check :
    cell277.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 4, 27, 6] witnessGeometryChecked (by decide))
      cell277_check_indexed

/-- Closed-cover cell 278 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 4, 27, 6]`; `cell278_check` verifies its
explicit-potential certificate. -/
def cell278 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell278_check_hints : cell278.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell278_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell278_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell278_check_hints

theorem cell278_check :
    cell278.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 4, 27, 6] witnessGeometryChecked (by decide))
      cell278_check_indexed

/-- Closed-cover cell 279 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 4, 27, 6]`; `cell279_check` verifies
its explicit-potential certificate. -/
def cell279 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell279_check_hints : cell279.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell279_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell279_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell279_check_hints

theorem cell279_check :
    cell279.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 4, 27, 6] witnessGeometryChecked (by decide))
      cell279_check_indexed

/-- Closed-cover cell 280 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 4, 27, 6]`; `cell280_check` verifies
its explicit-potential certificate. -/
def cell280 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 4, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell280_check_hints : cell280.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 19, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]] = true := by
  decide +kernel

private theorem cell280_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell280_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell280_check_hints

theorem cell280_check :
    cell280.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 4, 27, 6] witnessGeometryChecked (by decide))
      cell280_check_indexed

/-- Closed-cover cell 281 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 4, 28, 6]`; `cell281_check` verifies its
explicit-potential certificate. -/
def cell281 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell281_check_hints : cell281.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 6, 19, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21]]
     = true := by
  decide +kernel

private theorem cell281_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell281_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell281_check_hints

theorem cell281_check :
    cell281.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 3, 4, 28, 6] witnessGeometryChecked (by decide))
      cell281_check_indexed

/-- Closed-cover cell 282 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 4, 28, 6]`; `cell282_check` verifies its
explicit-potential certificate. -/
def cell282 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell282_check_hints : cell282.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell282_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell282_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell282_check_hints

theorem cell282_check :
    cell282.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 4, 28, 6] witnessGeometryChecked (by decide))
      cell282_check_indexed

/-- Closed-cover cell 283 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 4, 28, 6]`; `cell283_check` verifies its
explicit-potential certificate. -/
def cell283 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell283_check_hints : cell283.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell283_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell283_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell283_check_hints

theorem cell283_check :
    cell283.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 4, 28, 6] witnessGeometryChecked (by decide))
      cell283_check_indexed

/-- Closed-cover cell 284 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 4, 28, 6]`; `cell284_check` verifies
its explicit-potential certificate. -/
def cell284 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell284_check_hints : cell284.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell284_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell284_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell284_check_hints

theorem cell284_check :
    cell284.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 4, 28, 6] witnessGeometryChecked (by decide))
      cell284_check_indexed

/-- Closed-cover cell 285 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 4, 28, 6]`; `cell285_check` verifies
its explicit-potential certificate. -/
def cell285 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 4, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell285_check_hints : cell285.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell285_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell285_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell285_check_hints

theorem cell285_check :
    cell285.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 4, 28, 6] witnessGeometryChecked (by decide))
      cell285_check_indexed

/-- Closed-cover cell 286 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 4, 29, 6]`; `cell286_check` verifies its
explicit-potential certificate. -/
def cell286 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell286_check_hints : cell286.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 16, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 6, 19, 20], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 21]]
     = true := by
  decide +kernel

private theorem cell286_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell286_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell286_check_hints

theorem cell286_check :
    cell286.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 7, 2, 2, 3, 4, 29, 6] witnessGeometryChecked (by decide))
      cell286_check_indexed

/-- Closed-cover cell 287 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 4, 29, 6]`; `cell287_check` verifies its
explicit-potential certificate. -/
def cell287 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell287_check_hints : cell287.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 0, 0, 14, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 15, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 9], [0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 20]]
     = true := by
  decide +kernel

private theorem cell287_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell287_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell287_check_hints

theorem cell287_check :
    cell287.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 2, 2, 3, 4, 29, 6] witnessGeometryChecked (by decide))
      cell287_check_indexed

/-- Closed-cover cell 288 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 4, 29, 6]`; `cell288_check` verifies its
explicit-potential certificate. -/
def cell288 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell288_check_hints : cell288.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell288_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell288_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell288_check_hints

theorem cell288_check :
    cell288.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 9, 2, 2, 3, 4, 29, 6] witnessGeometryChecked (by decide))
      cell288_check_indexed

/-- Closed-cover cell 289 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 4, 29, 6]`; `cell289_check` verifies
its explicit-potential certificate. -/
def cell289 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell289_check_hints : cell289.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [0, 0, 14, 1, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 22]] = true := by
  decide +kernel

private theorem cell289_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell289_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell289_check_hints

theorem cell289_check :
    cell289.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 10, 2, 2, 3, 4, 29, 6] witnessGeometryChecked (by decide))
      cell289_check_indexed

/-- Closed-cover cell 290 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 4, 29, 6]`; `cell290_check` verifies
its explicit-potential certificate. -/
def cell290 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

private theorem cell290_check_hints : cell290.certificate.checkClosedRowsAtHints 4
    [[0, 0, 0, 0, 0, 0, 3, 13], [14, 15, 16, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 10], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 9], [0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 20, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 22]]
     = true := by
  decide +kernel

private theorem cell290_check_indexed :
    type_of% (CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell290_check_hints) := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_of_checkClosedRowsAtHints cell290_check_hints

theorem cell290_check :
    cell290.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row06Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 2, 2, 3, 4, 29, 6] witnessGeometryChecked (by decide))
      cell290_check_indexed

/-- The ordered row-06 closed-cover cell block with global indices 194 through 290, used when
assembling the full 483-cell cover. -/
def chunk : List (CoordinateCell row06Core) :=
  [cell194, cell195, cell196, cell197, cell198, cell199, cell200, cell201, cell202, cell203,
  cell204, cell205, cell206, cell207, cell208, cell209, cell210, cell211, cell212, cell213, cell214,
  cell215, cell216, cell217, cell218, cell219, cell220, cell221, cell222, cell223, cell224, cell225,
  cell226, cell227, cell228, cell229, cell230, cell231, cell232, cell233, cell234, cell235, cell236,
  cell237, cell238, cell239, cell240, cell241, cell242, cell243, cell244, cell245, cell246, cell247,
  cell248, cell249, cell250, cell251, cell252, cell253, cell254, cell255, cell256, cell257, cell258,
  cell259, cell260, cell261, cell262, cell263, cell264, cell265, cell266, cell267, cell268, cell269,
  cell270, cell271, cell272, cell273, cell274, cell275, cell276, cell277, cell278, cell279, cell280,
  cell281, cell282, cell283, cell284, cell285, cell286, cell287, cell288, cell289, cell290]

theorem chunk_check :
    chunk.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [chunk, cell194_check, cell195_check, cell196_check, cell197_check, cell198_check,
    cell199_check, cell200_check, cell201_check, cell202_check, cell203_check, cell204_check,
    cell205_check, cell206_check, cell207_check, cell208_check, cell209_check, cell210_check,
    cell211_check, cell212_check, cell213_check, cell214_check, cell215_check, cell216_check,
    cell217_check, cell218_check, cell219_check, cell220_check, cell221_check, cell222_check,
    cell223_check, cell224_check, cell225_check, cell226_check, cell227_check, cell228_check,
    cell229_check, cell230_check, cell231_check, cell232_check, cell233_check, cell234_check,
    cell235_check, cell236_check, cell237_check, cell238_check, cell239_check, cell240_check,
    cell241_check, cell242_check, cell243_check, cell244_check, cell245_check, cell246_check,
    cell247_check, cell248_check, cell249_check, cell250_check, cell251_check, cell252_check,
    cell253_check, cell254_check, cell255_check, cell256_check, cell257_check, cell258_check,
    cell259_check, cell260_check, cell261_check, cell262_check, cell263_check, cell264_check,
    cell265_check, cell266_check, cell267_check, cell268_check, cell269_check, cell270_check,
    cell271_check, cell272_check, cell273_check, cell274_check, cell275_check, cell276_check,
    cell277_check, cell278_check, cell279_check, cell280_check, cell281_check, cell282_check,
    cell283_check, cell284_check, cell285_check, cell286_check, cell287_check, cell288_check,
    cell289_check, cell290_check]

end AtanasovRanganathan.GenusFiveRow06CoverCells2
