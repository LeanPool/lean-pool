/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04CoverBase

/-! **Independent generated check.** This module provides an additional generated proof of row 04
and is not imported by the main `LowGenus` root.

Generated cell chunk 1 of 2 for the AR row-04 chamber cover
(cells 98-194).  Split across modules because the kernel cost of
replaying a cell is cumulative within one Lean process. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04CoverCells1

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow04CoverBase

/-- Closed-cover cell 98 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 29, 8, 0, 0, 24]`; `cell98_check` verifies its
explicit-potential certificate. -/
def cell98 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 29, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1,
      1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell98_check_indexed : cell98.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 18, 19, 18, 20], [0, 0, 13, 1, 0, 0, 0, 0,
     4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 7, 0, 0, 21, 22, 21, 23]] = true := by
  decide +kernel

theorem cell98_check :
    cell98.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 0, 29, 8, 0, 0, 24] witnessGeometryChecked (by decide))
      cell98_check_indexed

/-- Closed-cover cell 99 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 30, 8, 0, 0, 24]`; `cell99_check` verifies its
explicit-potential certificate. -/
def cell99 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 30, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell99_check_indexed : cell99.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 11, 20], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 17, 7, 0, 0, 21, 22, 21, 19]] = true := by
  decide +kernel

theorem cell99_check :
    cell99.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 0, 30, 8, 0, 0, 24] witnessGeometryChecked (by decide))
      cell99_check_indexed

/-- Closed-cover cell 100 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 21, 9, 0, 0, 22]`; `cell100_check` verifies
its explicit-potential certificate. -/
def cell100 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 21, 9, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

private theorem cell100_check_indexed : cell100.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 0,
     0, 0, 0, 11, 20], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     21, 22, 0, 0, 0, 0, 0, 0, 11, 20]] = true := by
  decide +kernel

theorem cell100_check :
    cell100.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 21, 9, 0, 0, 22] witnessGeometryChecked (by decide))
      cell100_check_indexed

/-- Closed-cover cell 101 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 26, 9, 0, 0, 5]`; `cell101_check` verifies
its explicit-potential certificate. -/
def cell101 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 26, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell101_check_indexed : cell101.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18,
     7, 0, 0, 0, 0, 10, 19, 20, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 7, 0, 0, 0, 0, 10, 19, 22, 23]] = true := by
  decide +kernel

theorem cell101_check :
    cell101.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 26, 9, 0, 0, 5] witnessGeometryChecked (by decide))
      cell101_check_indexed

/-- Closed-cover cell 102 for the fixed row-04 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 5, 9, 0, 0, 5]`; `cell102_check` verifies its
explicit-potential certificate. -/
def cell102 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 5, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell102_check_indexed : cell102.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18,
     7, 0, 0, 0, 0, 10, 19, 20, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 7, 0, 0, 0, 0, 10, 19, 20, 21]] = true := by
  decide +kernel

theorem cell102_check :
    cell102.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 5, 9, 0, 0, 5] witnessGeometryChecked (by decide))
      cell102_check_indexed

/-- Closed-cover cell 103 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 25, 9, 0, 0, 6]`; `cell103_check` verifies
its explicit-potential certificate. -/
def cell103 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 25, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0]] }

private theorem cell103_check_indexed : cell103.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18,
     7, 19, 20, 0, 0, 21, 22], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 18, 7, 19, 20, 0, 0, 10, 22]] = true := by
  decide +kernel

theorem cell103_check :
    cell103.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 25, 9, 0, 0, 6] witnessGeometryChecked (by decide))
      cell103_check_indexed

/-- Closed-cover cell 104 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 27, 9, 0, 0, 28]`; `cell104_check` verifies
its explicit-potential certificate. -/
def cell104 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 27, 9, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

private theorem cell104_check_indexed : cell104.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19, 0, 0, 0, 0, 10, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 22, 7, 18, 23, 0, 0, 24, 21]] = true := by
  decide +kernel

theorem cell104_check :
    cell104.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 27, 9, 0, 0, 28] witnessGeometryChecked (by decide))
      cell104_check_indexed

/-- Closed-cover cell 105 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 27, 9, 0, 0, 7]`; `cell105_check` verifies
its explicit-potential certificate. -/
def cell105 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 27, 9, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0,
      -1]] }

private theorem cell105_check_indexed : cell105.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19, 0, 0, 0, 0, 10, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 22, 23, 24, 23, 0, 0, 0, 0, 10, 21]] = true := by
  decide +kernel

theorem cell105_check :
    cell105.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 27, 9, 0, 0, 7] witnessGeometryChecked (by decide))
      cell105_check_indexed

/-- Closed-cover cell 106 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 23, 9, 0, 0, 24]`; `cell106_check` verifies
its explicit-potential certificate. -/
def cell106 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 23, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell106_check_indexed : cell106.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18,
     7, 19, 20, 0, 0, 10, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 18, 7, 0, 0, 22, 20, 22, 23]] = true := by
  decide +kernel

theorem cell106_check :
    cell106.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 23, 9, 0, 0, 24] witnessGeometryChecked (by decide))
      cell106_check_indexed

/-- Closed-cover cell 107 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 29, 9, 0, 0, 24]`; `cell107_check` verifies
its explicit-potential certificate. -/
def cell107 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 29, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1,
      1]] }

private theorem cell107_check_indexed : cell107.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18,
     7, 0, 0, 19, 20, 19, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 18, 7, 0, 0, 22, 23, 22, 24]] = true := by
  decide +kernel

theorem cell107_check :
    cell107.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 29, 9, 0, 0, 24] witnessGeometryChecked (by decide))
      cell107_check_indexed

/-- Closed-cover cell 108 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 30, 9, 0, 0, 24]`; `cell108_check` verifies
its explicit-potential certificate. -/
def cell108 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 30, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell108_check_indexed : cell108.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18,
     7, 19, 20, 11, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 18, 7, 0, 0, 22, 23, 22, 20]] = true := by
  decide +kernel

theorem cell108_check :
    cell108.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 30, 9, 0, 0, 24] witnessGeometryChecked (by decide))
      cell108_check_indexed

/-- Closed-cover cell 109 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 26, 18, 0, 0, 5]`; `cell109_check` verifies
its explicit-potential certificate. -/
def cell109 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 26, 18, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell109_check_indexed : cell109.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 21, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 24, 25]] = true := by
  decide +kernel

theorem cell109_check :
    cell109.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 26, 18, 0, 0, 5] witnessGeometryChecked (by decide))
      cell109_check_indexed

/-- Closed-cover cell 110 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 26, 10, 0, 0, 5]`; `cell110_check` verifies
its explicit-potential certificate. -/
def cell110 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 26, 10, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1,
      0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell110_check_indexed : cell110.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 0, 0, 21, 22, 21, 23], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 24, 25]] = true := by
  decide +kernel

theorem cell110_check :
    cell110.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 26, 10, 0, 0, 5] witnessGeometryChecked (by decide))
      cell110_check_indexed

/-- Closed-cover cell 111 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 26, 18, 0, 0, 24]`; `cell111_check` verifies
its explicit-potential certificate. -/
def cell111 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 26, 18, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0,
      1, 1]] }

private theorem cell111_check_indexed : cell111.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 21, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 25, 24, 26]] = true := by
  decide +kernel

theorem cell111_check :
    cell111.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 26, 18, 0, 0, 24] witnessGeometryChecked (by decide))
      cell111_check_indexed

/-- Closed-cover cell 112 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 26, 10, 0, 0, 24]`; `cell112_check` verifies
its explicit-potential certificate. -/
def cell112 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 26, 10, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0,
      1, 1]] }

private theorem cell112_check_indexed : cell112.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 0, 0, 21, 22, 21, 23], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 25, 24, 26]] = true := by
  decide +kernel

theorem cell112_check :
    cell112.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 26, 10, 0, 0, 24] witnessGeometryChecked (by decide))
      cell112_check_indexed

/-- Closed-cover cell 113 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 5, 18, 0, 0, 5]`; `cell113_check` verifies
its explicit-potential certificate. -/
def cell113 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 5, 18, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell113_check_indexed : cell113.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 21, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20]] = true := by
  decide +kernel

theorem cell113_check :
    cell113.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 5, 18, 0, 0, 5] witnessGeometryChecked (by decide))
      cell113_check_indexed

/-- Closed-cover cell 114 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 5, 10, 0, 0, 5]`; `cell114_check` verifies
its explicit-potential certificate. -/
def cell114 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 5, 10, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1],
      aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]] }

private theorem cell114_check_indexed : cell114.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 0, 0, 21, 22, 21, 23], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20]] = true := by
  decide +kernel

theorem cell114_check :
    cell114.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 5, 10, 0, 0, 5] witnessGeometryChecked (by decide))
      cell114_check_indexed

/-- Closed-cover cell 115 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 25, 18, 0, 0, 6]`; `cell115_check` verifies
its explicit-potential certificate. -/
def cell115 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 25, 18, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell115_check_indexed : cell115.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 0, 0, 20, 21], [0, 0, 13, 22, 23, 15, 0, 0, 4, 24], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 21]] = true := by
  decide +kernel

theorem cell115_check :
    cell115.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 25, 18, 0, 0, 6] witnessGeometryChecked (by decide))
      cell115_check_indexed

/-- Closed-cover cell 116 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 25, 10, 0, 0, 6]`; `cell116_check` verifies
its explicit-potential certificate. -/
def cell116 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 25, 10, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0,
      -1]] }

private theorem cell116_check_indexed : cell116.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 0, 0, 20, 21], [0, 0, 13, 1, 0, 0, 22, 23, 22, 24], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 21]] = true := by
  decide +kernel

theorem cell116_check :
    cell116.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 25, 10, 0, 0, 6] witnessGeometryChecked (by decide))
      cell116_check_indexed

/-- Closed-cover cell 117 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 18, 0, 0, 28]`; `cell117_check` verifies
its explicit-potential certificate. -/
def cell117 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 18, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

private theorem cell117_check_indexed : cell117.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 21, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 24, 7, 17, 25, 0, 0, 26, 20]] = true := by
  decide +kernel

theorem cell117_check :
    cell117.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 18, 0, 0, 28] witnessGeometryChecked (by decide))
      cell117_check_indexed

/-- Closed-cover cell 118 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 18, 0, 0, 7]`; `cell118_check` verifies
its explicit-potential certificate. -/
def cell118 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 18, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0,
      -1]] }

private theorem cell118_check_indexed : cell118.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 21, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 24, 25, 26, 25, 0, 0, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell118_check :
    cell118.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 18, 0, 0, 7] witnessGeometryChecked (by decide))
      cell118_check_indexed

/-- Closed-cover cell 119 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 10, 0, 0, 28]`; `cell119_check` verifies
its explicit-potential certificate. -/
def cell119 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 10, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

private theorem cell119_check_indexed : cell119.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 21, 22, 21, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 24, 7, 17, 25, 0, 0, 26, 20]] = true := by
  decide +kernel

theorem cell119_check :
    cell119.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 10, 0, 0, 28] witnessGeometryChecked (by decide))
      cell119_check_indexed

/-- Closed-cover cell 120 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 10, 0, 0, 7]`; `cell120_check` verifies
its explicit-potential certificate. -/
def cell120 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 10, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0,
      -1]] }

private theorem cell120_check_indexed : cell120.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 21, 22, 21, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 24, 25, 26, 25, 0, 0, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell120_check :
    cell120.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 10, 0, 0, 7] witnessGeometryChecked (by decide))
      cell120_check_indexed

/-- Closed-cover cell 121 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 23, 18, 0, 0, 24]`; `cell121_check` verifies
its explicit-potential certificate. -/
def cell121 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 23, 18, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell121_check_indexed : cell121.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 0, 0, 10, 20], [0, 0, 13, 21, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 19, 24, 25]] = true := by
  decide +kernel

theorem cell121_check :
    cell121.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 23, 18, 0, 0, 24] witnessGeometryChecked (by decide))
      cell121_check_indexed

/-- Closed-cover cell 122 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 23, 10, 0, 0, 24]`; `cell122_check` verifies
its explicit-potential certificate. -/
def cell122 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 23, 10, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell122_check_indexed : cell122.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 21, 22, 21, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 19, 24, 25]] = true := by
  decide +kernel

theorem cell122_check :
    cell122.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 23, 10, 0, 0, 24] witnessGeometryChecked (by decide))
      cell122_check_indexed

/-- Closed-cover cell 123 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 29, 18, 0, 0, 24]`; `cell123_check` verifies
its explicit-potential certificate. -/
def cell123 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 29, 18, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1,
      1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0,
      1, 1]] }

private theorem cell123_check_indexed : cell123.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 18, 19, 18, 20], [0, 0, 13, 21, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 25, 24, 26]] = true := by
  decide +kernel

theorem cell123_check :
    cell123.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 29, 18, 0, 0, 24] witnessGeometryChecked (by decide))
      cell123_check_indexed

/-- Closed-cover cell 124 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 29, 10, 0, 0, 24]`; `cell124_check` verifies
its explicit-potential certificate. -/
def cell124 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 29, 10, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1,
      1], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0,
      1, 1]] }

private theorem cell124_check_indexed : cell124.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 18, 19, 18, 20], [0, 0, 13, 1, 0, 0, 21, 22, 21, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 25, 24, 26]] = true := by
  decide +kernel

theorem cell124_check :
    cell124.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 29, 10, 0, 0, 24] witnessGeometryChecked (by decide))
      cell124_check_indexed

/-- Closed-cover cell 125 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 21, 14, 0, 0, 22]`; `cell125_check` verifies
its explicit-potential certificate. -/
def cell125 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 21, 14, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1,
      -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

private theorem cell125_check_indexed : cell125.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0,
     0, 0, 0, 11, 19], [14, 20, 21, 20, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     22, 23, 0, 0, 0, 0, 0, 0, 11, 19]] = true := by
  decide +kernel

theorem cell125_check :
    cell125.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 21, 14, 0, 0, 22] witnessGeometryChecked (by decide))
      cell125_check_indexed

/-- Closed-cover cell 126 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 5, 14, 0, 0, 5]`; `cell126_check` verifies
its explicit-potential certificate. -/
def cell126 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 5, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]] }

private theorem cell126_check_indexed : cell126.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     0, 0, 0, 0, 10, 18, 19, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20]] = true := by
  decide +kernel

theorem cell126_check :
    cell126.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 5, 14, 0, 0, 5] witnessGeometryChecked (by decide))
      cell126_check_indexed

/-- Closed-cover cell 127 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 26, 14, 0, 0, 5]`; `cell127_check` verifies
its explicit-potential certificate. -/
def cell127 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 26, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1]] }

private theorem cell127_check_indexed : cell127.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     0, 0, 0, 0, 10, 18, 19, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 23, 24]] = true := by
  decide +kernel

theorem cell127_check :
    cell127.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 26, 14, 0, 0, 5] witnessGeometryChecked (by decide))
      cell127_check_indexed

/-- Closed-cover cell 128 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 25, 14, 0, 0, 6]`; `cell128_check` verifies
its explicit-potential certificate. -/
def cell128 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 25, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]] }

private theorem cell128_check_indexed : cell128.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     18, 19, 0, 0, 20, 21], [14, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 21]] = true := by
  decide +kernel

theorem cell128_check :
    cell128.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 25, 14, 0, 0, 6] witnessGeometryChecked (by decide))
      cell128_check_indexed

/-- Closed-cover cell 129 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 27, 14, 0, 0, 28]`; `cell129_check` verifies
its explicit-potential certificate. -/
def cell129 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 27, 14, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

private theorem cell129_check_indexed : cell129.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 23, 7, 17, 24, 0, 0, 25, 20]] = true := by
  decide +kernel

theorem cell129_check :
    cell129.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 27, 14, 0, 0, 28] witnessGeometryChecked (by decide))
      cell129_check_indexed

/-- Closed-cover cell 130 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 27, 14, 0, 0, 7]`; `cell130_check` verifies
its explicit-potential certificate. -/
def cell130 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 27, 14, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

private theorem cell130_check_indexed : cell130.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 23, 24, 25, 24, 0, 0, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell130_check :
    cell130.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 27, 14, 0, 0, 7] witnessGeometryChecked (by decide))
      cell130_check_indexed

/-- Closed-cover cell 131 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 23, 14, 0, 0, 24]`; `cell131_check` verifies
its explicit-potential certificate. -/
def cell131 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 23, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell131_check_indexed : cell131.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     18, 19, 0, 0, 10, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 19, 23, 24]] = true := by
  decide +kernel

theorem cell131_check :
    cell131.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 23, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell131_check_indexed

/-- Closed-cover cell 132 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 29, 14, 0, 0, 24]`; `cell132_check` verifies
its explicit-potential certificate. -/
def cell132 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 29, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1,
      1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell132_check_indexed : cell132.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     0, 0, 18, 19, 18, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 25]] = true := by
  decide +kernel

theorem cell132_check :
    cell132.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 29, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell132_check_indexed

/-- Closed-cover cell 133 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 30, 14, 0, 0, 24]`; `cell133_check` verifies
its explicit-potential certificate. -/
def cell133 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 30, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell133_check_indexed : cell133.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     18, 19, 11, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 19]] = true := by
  decide +kernel

theorem cell133_check :
    cell133.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 30, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell133_check_indexed

/-- Closed-cover cell 134 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 21, 14, 0, 0, 22]`; `cell134_check` verifies
its explicit-potential certificate. -/
def cell134 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 21, 14, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

private theorem cell134_check_indexed : cell134.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0,
     0, 0, 0, 11, 19], [20, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     23, 24, 0, 0, 0, 0, 0, 0, 11, 19]] = true := by
  decide +kernel

theorem cell134_check :
    cell134.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 21, 14, 0, 0, 22] witnessGeometryChecked (by decide))
      cell134_check_indexed

/-- Closed-cover cell 135 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 5, 14, 0, 0, 5]`; `cell135_check` verifies
its explicit-potential certificate. -/
def cell135 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 5, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]] }

private theorem cell135_check_indexed : cell135.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [21, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20]] = true := by
  decide +kernel

theorem cell135_check :
    cell135.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 5, 14, 0, 0, 5] witnessGeometryChecked (by decide))
      cell135_check_indexed

/-- Closed-cover cell 136 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 23, 14, 0, 0, 24]`; `cell136_check` verifies
its explicit-potential certificate. -/
def cell136 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 23, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell136_check_indexed : cell136.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 0, 0, 10, 20], [21, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 19, 24, 25]] = true := by
  decide +kernel

theorem cell136_check :
    cell136.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 23, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell136_check_indexed

/-- Closed-cover cell 137 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 26, 14, 0, 0, 5]`; `cell137_check` verifies
its explicit-potential certificate. -/
def cell137 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 26, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell137_check_indexed : cell137.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [21, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 24, 25]] = true := by
  decide +kernel

theorem cell137_check :
    cell137.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 26, 14, 0, 0, 5] witnessGeometryChecked (by decide))
      cell137_check_indexed

/-- Closed-cover cell 138 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 25, 14, 0, 0, 6]`; `cell138_check` verifies
its explicit-potential certificate. -/
def cell138 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 25, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]] }

private theorem cell138_check_indexed : cell138.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 0, 0, 20, 21], [22, 23, 24, 23, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 21]] = true := by
  decide +kernel

theorem cell138_check :
    cell138.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 25, 14, 0, 0, 6] witnessGeometryChecked (by decide))
      cell138_check_indexed

/-- Closed-cover cell 139 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 27, 14, 0, 0, 28]`; `cell139_check` verifies
its explicit-potential certificate. -/
def cell139 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 27, 14, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

private theorem cell139_check_indexed : cell139.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [21, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 24, 7, 17, 25, 0, 0, 26, 20]] = true := by
  decide +kernel

theorem cell139_check :
    cell139.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 27, 14, 0, 0, 28] witnessGeometryChecked (by decide))
      cell139_check_indexed

/-- Closed-cover cell 140 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 27, 14, 0, 0, 7]`; `cell140_check` verifies
its explicit-potential certificate. -/
def cell140 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 27, 14, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0,
      -1]] }

private theorem cell140_check_indexed : cell140.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [21, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 24, 25, 26, 25, 0, 0, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell140_check :
    cell140.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 27, 14, 0, 0, 7] witnessGeometryChecked (by decide))
      cell140_check_indexed

/-- Closed-cover cell 141 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 29, 14, 0, 0, 24]`; `cell141_check` verifies
its explicit-potential certificate. -/
def cell141 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 29, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1,
      1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0,
      1, 1]] }

private theorem cell141_check_indexed : cell141.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 18, 19, 18, 20], [21, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 25, 24, 26]] = true := by
  decide +kernel

theorem cell141_check :
    cell141.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 29, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell141_check_indexed

/-- Closed-cover cell 142 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 26, 8, 0, 0, 5]`; `cell142_check` verifies
its explicit-potential certificate. -/
def cell142 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 26, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1,
      0, 1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0,
      0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0,
      1, 0, 1]] }

private theorem cell142_check_indexed : cell142.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 0, 0,
     0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 23, 24]] = true := by
  decide +kernel

theorem cell142_check :
    cell142.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 26, 8, 0, 0, 5] witnessGeometryChecked (by decide))
      cell142_check_indexed

/-- Closed-cover cell 143 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 26, 8, 0, 0, 24]`; `cell143_check` verifies
its explicit-potential certificate. -/
def cell143 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 26, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1,
      0, 1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0,
      0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1,
      0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell143_check_indexed : cell143.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 0, 0,
     0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 25]] = true := by
  decide +kernel

theorem cell143_check :
    cell143.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 26, 8, 0, 0, 24] witnessGeometryChecked (by decide))
      cell143_check_indexed

/-- Closed-cover cell 144 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 26, 14, 0, 0, 5]`; `cell144_check` verifies
its explicit-potential certificate. -/
def cell144 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 26, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1,
      0, 1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
      0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1,
      0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell144_check_indexed : cell144.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20], [21, 22, 23, 22, 0,
     0, 0, 0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10,
     18, 24, 25]] = true := by
  decide +kernel

theorem cell144_check :
    cell144.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 26, 14, 0, 0, 5] witnessGeometryChecked (by decide))
      cell144_check_indexed

/-- Closed-cover cell 145 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 26, 14, 0, 0, 24]`; `cell145_check` verifies
its explicit-potential certificate. -/
def cell145 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 26, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1,
      0, 1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
      0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
      0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0,
      0, 1, 1]] }

private theorem cell145_check_indexed : cell145.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20], [21, 22, 23, 22, 0,
     0, 0, 0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 25, 24,
     26]] = true := by
  decide +kernel

theorem cell145_check :
    cell145.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 26, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell145_check_indexed

/-- Closed-cover cell 146 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 26, 8, 0, 0, 24]`; `cell146_check` verifies
its explicit-potential certificate. -/
def cell146 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 26, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell146_check_indexed : cell146.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 0, 0,
     0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 7, 0, 0, 21, 22, 21, 23]] = true := by
  decide +kernel

theorem cell146_check :
    cell146.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 0, 26, 8, 0, 0, 24] witnessGeometryChecked (by decide))
      cell146_check_indexed

/-- Closed-cover cell 147 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 26, 14, 0, 0, 24]`; `cell147_check` verifies
its explicit-potential certificate. -/
def cell147 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 26, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell147_check_indexed : cell147.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     0, 0, 0, 0, 10, 18, 19, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 25]] = true := by
  decide +kernel

theorem cell147_check :
    cell147.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 26, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell147_check_indexed

/-- Closed-cover cell 148 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 26, 9, 0, 0, 24]`; `cell148_check` verifies
its explicit-potential certificate. -/
def cell148 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 26, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1,
      1]] }

private theorem cell148_check_indexed : cell148.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18,
     7, 0, 0, 0, 0, 10, 19, 20, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 7, 0, 0, 22, 23, 22, 24]] = true := by
  decide +kernel

theorem cell148_check :
    cell148.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 26, 9, 0, 0, 24] witnessGeometryChecked (by decide))
      cell148_check_indexed

/-- Closed-cover cell 149 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 26, 14, 0, 0, 24]`; `cell149_check` verifies
its explicit-potential certificate. -/
def cell149 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 26, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0,
      1, 1]] }

private theorem cell149_check_indexed : cell149.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [21, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 25, 24, 26]] = true := by
  decide +kernel

theorem cell149_check :
    cell149.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 26, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell149_check_indexed

/-- Closed-cover cell 150 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 0, 29, 12, 0, 0, 24]`; `cell150_check` verifies
its explicit-potential certificate. -/
def cell150 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 0, 29, 12, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1], aff [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1,
      1]] }

private theorem cell150_check_indexed : cell150.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     16, 7, 0, 0, 17, 18, 17, 19], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21], [], [], [0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 7, 0, 0, 22, 23, 22, 24]] = true := by
  decide +kernel

theorem cell150_check :
    cell150.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 0, 29, 12, 0, 0, 24] witnessGeometryChecked (by decide))
      cell150_check_indexed

/-- Closed-cover cell 151 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 29, 8, 0, 0, 24]`; `cell151_check` verifies
its explicit-potential certificate. -/
def cell151 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 29, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0,
      1, 1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0,
      0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1,
      0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell151_check_indexed : cell151.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 18, 19, 18, 20], [0, 0, 13, 1, 0, 0, 0, 0,
     4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 25]] = true := by
  decide +kernel

theorem cell151_check :
    cell151.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 29, 8, 0, 0, 24] witnessGeometryChecked (by decide))
      cell151_check_indexed

/-- Closed-cover cell 152 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 20, 0, 29, 14, 0, 0, 24]`; `cell152_check` verifies
its explicit-potential certificate. -/
def cell152 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 20, 0, 29, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1,
      1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell152_check_indexed : cell152.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     0, 0, 18, 19, 18, 20], [21, 22, 14, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 25]] = true := by
  decide +kernel

theorem cell152_check :
    cell152.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 20, 0, 29, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell152_check_indexed

/-- Closed-cover cell 153 for the fixed row-04 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 0, 5, 12, 0, 0, 5]`; `cell153_check` verifies
its explicit-potential certificate. -/
def cell153 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 0, 5, 12, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]] }

private theorem cell153_check_indexed : cell153.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     16, 7, 0, 0, 0, 0, 10, 17, 18, 19], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21], [], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 7, 0, 0, 0, 0, 10, 17, 18, 19]] = true := by
  decide +kernel

theorem cell153_check :
    cell153.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 0, 5, 12, 0, 0, 5] witnessGeometryChecked (by decide))
      cell153_check_indexed

/-- Closed-cover cell 154 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 5, 8, 0, 0, 5]`; `cell154_check` verifies its
explicit-potential certificate. -/
def cell154 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 5, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1]] }

private theorem cell154_check_indexed : cell154.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 0, 0,
     0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20]] = true := by
  decide +kernel

theorem cell154_check :
    cell154.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 5, 8, 0, 0, 5] witnessGeometryChecked (by decide))
      cell154_check_indexed

/-- Closed-cover cell 155 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 20, 0, 5, 14, 0, 0, 5]`; `cell155_check` verifies
its explicit-potential certificate. -/
def cell155 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 20, 0, 5, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]] }

private theorem cell155_check_indexed : cell155.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     0, 0, 0, 0, 10, 18, 19, 20], [21, 22, 14, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20]] = true := by
  decide +kernel

theorem cell155_check :
    cell155.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 20, 0, 5, 14, 0, 0, 5] witnessGeometryChecked (by decide))
      cell155_check_indexed

/-- Closed-cover cell 156 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 0, 23, 12, 0, 0, 24]`; `cell156_check` verifies
its explicit-potential certificate. -/
def cell156 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 0, 23, 12, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell156_check_indexed : cell156.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     16, 7, 17, 18, 0, 0, 10, 19], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21], [], [], [0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 7, 0, 0, 22, 18, 22, 23]] = true := by
  decide +kernel

theorem cell156_check :
    cell156.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 0, 23, 12, 0, 0, 24] witnessGeometryChecked (by decide))
      cell156_check_indexed

/-- Closed-cover cell 157 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 23, 8, 0, 0, 24]`; `cell157_check` verifies
its explicit-potential certificate. -/
def cell157 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 23, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1,
      1]] }

private theorem cell157_check_indexed : cell157.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 0, 0,
     4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 7, 0, 0, 23, 19, 23, 24]] = true := by
  decide +kernel

theorem cell157_check :
    cell157.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 23, 8, 0, 0, 24] witnessGeometryChecked (by decide))
      cell157_check_indexed

/-- Closed-cover cell 158 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 23, 14, 0, 0, 24]`; `cell158_check` verifies
its explicit-potential certificate. -/
def cell158 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 23, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell158_check_indexed : cell158.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 20], [21, 22, 23, 22, 0, 0, 0,
     0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 19, 24, 25]]
     = true := by
  decide +kernel

theorem cell158_check :
    cell158.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 23, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell158_check_indexed

/-- Closed-cover cell 159 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 20, 0, 23, 14, 0, 0, 24]`; `cell159_check` verifies
its explicit-potential certificate. -/
def cell159 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 20, 0, 23, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell159_check_indexed : cell159.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7,
     18, 19, 0, 0, 10, 20], [21, 22, 14, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 19, 23, 24]] = true := by
  decide +kernel

theorem cell159_check :
    cell159.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 20, 0, 23, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell159_check_indexed

/-- Closed-cover cell 160 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 0, 27, 12, 0, 0, 6]`; `cell160_check` verifies
its explicit-potential certificate. -/
def cell160 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 0, 27, 12, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell160_check_indexed : cell160.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17,
     18, 17, 0, 0, 0, 0, 10, 19], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 7, 16, 23, 0, 0, 10, 19]] = true := by
  decide +kernel

theorem cell160_check :
    cell160.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 0, 27, 12, 0, 0, 6] witnessGeometryChecked (by decide))
      cell160_check_indexed

/-- Closed-cover cell 161 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 27, 8, 0, 0, 6]`; `cell161_check` verifies
its explicit-potential certificate. -/
def cell161 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 27, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0,
      1]] }

private theorem cell161_check_indexed : cell161.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 0, 0,
     4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 23, 7, 17, 24, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell161_check :
    cell161.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 27, 8, 0, 0, 6] witnessGeometryChecked (by decide))
      cell161_check_indexed

/-- Closed-cover cell 162 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 27, 14, 0, 0, 6]`; `cell162_check` verifies
its explicit-potential certificate. -/
def cell162 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 27, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0,
      0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell162_check_indexed : cell162.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18, 0, 0, 0, 0, 10, 20], [21, 22, 23, 22, 0, 0, 0,
     0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 7, 17, 25, 0, 0, 10, 20]]
     = true := by
  decide +kernel

theorem cell162_check :
    cell162.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 27, 14, 0, 0, 6] witnessGeometryChecked (by decide))
      cell162_check_indexed

/-- Closed-cover cell 163 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 27, 14, 0, 0, 6]`; `cell163_check` verifies
its explicit-potential certificate. -/
def cell163 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 27, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell163_check_indexed : cell163.certificate.checkClosedRows 4
    [[], [13, 14, 15, 14, 0, 0, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [21, 22, 23, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 24, 7, 17, 25, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell163_check :
    cell163.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 19, 0, 27, 14, 0, 0, 6] witnessGeometryChecked (by decide))
      cell163_check_indexed

/-- Closed-cover cell 164 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 20, 0, 27, 14, 0, 0, 6]`; `cell164_check` verifies
its explicit-potential certificate. -/
def cell164 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 20, 0, 27, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell164_check_indexed : cell164.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [21, 22, 14, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 23, 7, 17, 24, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell164_check :
    cell164.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 20, 0, 27, 14, 0, 0, 6] witnessGeometryChecked (by decide))
      cell164_check_indexed

/-- Closed-cover cell 165 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 27, 8, 0, 0, 6]`; `cell165_check` verifies its
explicit-potential certificate. -/
def cell165 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 27, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell165_check_indexed : cell165.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 0, 0,
     4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 21, 7, 17, 22, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell165_check :
    cell165.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 8, 0, 27, 8, 0, 0, 6] witnessGeometryChecked (by decide))
      cell165_check_indexed

/-- Closed-cover cell 166 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 27, 14, 0, 0, 6]`; `cell166_check` verifies
its explicit-potential certificate. -/
def cell166 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 27, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell166_check_indexed : cell166.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [14, 21, 22, 21, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 23, 7, 17, 24, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell166_check :
    cell166.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 13, 0, 27, 14, 0, 0, 6] witnessGeometryChecked (by decide))
      cell166_check_indexed

/-- Closed-cover cell 167 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 27, 9, 0, 0, 6]`; `cell167_check` verifies
its explicit-potential certificate. -/
def cell167 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 27, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell167_check_indexed : cell167.certificate.checkClosedRows 4
    [[], [0, 0, 13, 14, 15, 16, 0, 0, 4, 17], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20,
     19, 0, 0, 0, 0, 10, 21], [0, 0, 13, 1, 15, 16, 0, 0, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 22, 7, 18, 23, 0, 0, 10, 21]] = true := by
  decide +kernel

theorem cell167_check :
    cell167.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 16, 0, 27, 9, 0, 0, 6] witnessGeometryChecked (by decide))
      cell167_check_indexed

/-- Closed-cover cell 168 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 18, 0, 0, 6]`; `cell168_check` verifies
its explicit-potential certificate. -/
def cell168 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 18, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell168_check_indexed : cell168.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 21, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 24, 7, 17, 25, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell168_check :
    cell168.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 18, 0, 0, 6] witnessGeometryChecked (by decide))
      cell168_check_indexed

/-- Closed-cover cell 169 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 10, 0, 0, 6]`; `cell169_check` verifies
its explicit-potential certificate. -/
def cell169 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 10, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell169_check_indexed : cell169.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 21, 22, 21, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 24, 7, 17, 25, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell169_check :
    cell169.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 10, 0, 0, 6] witnessGeometryChecked (by decide))
      cell169_check_indexed

/-- Closed-cover cell 170 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 0, 27, 12, 0, 0, 7]`; `cell170_check` verifies
its explicit-potential certificate. -/
def cell170 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 0, 27, 12, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0,
      -1]] }

private theorem cell170_check_indexed : cell170.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17,
     18, 17, 0, 0, 0, 0, 10, 19], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 22, 23, 24, 23, 0, 0, 0, 0, 10, 19]] = true := by
  decide +kernel

theorem cell170_check :
    cell170.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 11, 0, 27, 12, 0, 0, 7] witnessGeometryChecked (by decide))
      cell170_check_indexed

/-- Closed-cover cell 171 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 27, 8, 0, 0, 7]`; `cell171_check` verifies
its explicit-potential certificate. -/
def cell171 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 27, 8, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1,
      0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

private theorem cell171_check_indexed : cell171.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 0, 0,
     4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 23, 24, 25, 24, 0, 0, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell171_check :
    cell171.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 27, 8, 0, 0, 7] witnessGeometryChecked (by decide))
      cell171_check_indexed

/-- Closed-cover cell 172 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 27, 14, 0, 0, 7]`; `cell172_check` verifies
its explicit-potential certificate. -/
def cell172 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 27, 14, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1,
      0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1,
      0, -1]] }

private theorem cell172_check_indexed : cell172.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18, 0, 0, 0, 0, 10, 20], [21, 22, 23, 22, 0, 0, 0,
     0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 26, 25, 0, 0, 0, 0, 10, 20]]
     = true := by
  decide +kernel

theorem cell172_check :
    cell172.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 27, 14, 0, 0, 7] witnessGeometryChecked (by decide))
      cell172_check_indexed

/-- Closed-cover cell 173 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 20, 0, 27, 14, 0, 0, 7]`; `cell173_check` verifies
its explicit-potential certificate. -/
def cell173 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 20, 0, 27, 14, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, -1, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

private theorem cell173_check_indexed : cell173.certificate.checkClosedRows 4
    [[], [13, 2, 0, 0, 14, 15, 0, 0, 4, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [21, 22, 14, 22, 0, 0, 0, 0, 4, 16], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 23, 24, 25, 24, 0, 0, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell173_check :
    cell173.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 20, 0, 27, 14, 0, 0, 7] witnessGeometryChecked (by decide))
      cell173_check_indexed

/-- Closed-cover cell 174 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 21, 8, 0, 0, 22]`; `cell174_check` verifies
its explicit-potential certificate. -/
def cell174 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 21, 8, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1,
      -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

private theorem cell174_check_indexed : cell174.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 11, 19], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23,
     0, 0, 0, 0, 0, 0, 11, 19]] = true := by
  decide +kernel

theorem cell174_check :
    cell174.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 21, 8, 0, 0, 22] witnessGeometryChecked (by decide))
      cell174_check_indexed

/-- Closed-cover cell 175 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 25, 8, 0, 0, 6]`; `cell175_check` verifies
its explicit-potential certificate. -/
def cell175 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 25, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]] }

private theorem cell175_check_indexed : cell175.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 20, 21], [0, 0, 13, 1, 0, 0, 0, 0,
     4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 21]] = true := by
  decide +kernel

theorem cell175_check :
    cell175.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 25, 8, 0, 0, 6] witnessGeometryChecked (by decide))
      cell175_check_indexed

/-- Closed-cover cell 176 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 27, 8, 0, 0, 28]`; `cell176_check` verifies
its explicit-potential certificate. -/
def cell176 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 27, 8, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

private theorem cell176_check_indexed : cell176.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 0, 0, 0, 0,
     4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 23, 7, 17, 24, 0, 0, 25, 20]] = true := by
  decide +kernel

theorem cell176_check :
    cell176.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 27, 8, 0, 0, 28] witnessGeometryChecked (by decide))
      cell176_check_indexed

/-- Closed-cover cell 177 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 21, 14, 0, 0, 22]`; `cell177_check` verifies
its explicit-potential certificate. -/
def cell177 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 21, 14, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
      1]] }

private theorem cell177_check_indexed : cell177.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 11, 19], [20, 21, 22, 21, 0, 0, 0, 0, 4,
     14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 24, 0, 0, 0, 0, 0, 0, 11, 19]] = true := by
  decide +kernel

theorem cell177_check :
    cell177.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 21, 14, 0, 0, 22] witnessGeometryChecked (by decide))
      cell177_check_indexed

/-- Closed-cover cell 178 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 2, 14, 0, 0, 4]`; `cell178_check` verifies
its explicit-potential certificate. -/
def cell178 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 2, 14, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
      1]] }

private theorem cell178_check_indexed : cell178.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 0, 0, 10, 19], [20, 21, 22, 21, 0, 0, 0, 0,
     4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 24, 0, 0, 0, 0, 0, 0, 0, 0, 10, 19]]
     = true := by
  decide +kernel

theorem cell178_check :
    cell178.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 2, 14, 0, 0, 4] witnessGeometryChecked (by decide))
      cell178_check_indexed

/-- Closed-cover cell 179 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 29, 14, 0, 0, 24]`; `cell179_check` verifies
its explicit-potential certificate. -/
def cell179 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 29, 14, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0,
      1, 1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
      0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
      0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0,
      0, 1, 1]] }

private theorem cell179_check_indexed : cell179.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 18, 19, 18, 20], [21, 22, 23, 22, 0, 0, 0,
     0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 24, 25, 24, 26]]
     = true := by
  decide +kernel

theorem cell179_check :
    cell179.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 29, 14, 0, 0, 24] witnessGeometryChecked (by decide))
      cell179_check_indexed

/-- Closed-cover cell 180 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 5, 14, 0, 0, 5]`; `cell180_check` verifies
its explicit-potential certificate. -/
def cell180 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 5, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]] }

private theorem cell180_check_indexed : cell180.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20], [21, 22, 23, 22, 0,
     0, 0, 0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10,
     18, 19, 20]] = true := by
  decide +kernel

theorem cell180_check :
    cell180.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 5, 14, 0, 0, 5] witnessGeometryChecked (by decide))
      cell180_check_indexed

/-- Closed-cover cell 181 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 25, 14, 0, 0, 6]`; `cell181_check` verifies
its explicit-potential certificate. -/
def cell181 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 25, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0,
      -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0,
      1]] }

private theorem cell181_check_indexed : cell181.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 20, 21], [22, 23, 24, 23, 0, 0, 0,
     0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 21]]
     = true := by
  decide +kernel

theorem cell181_check :
    cell181.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 25, 14, 0, 0, 6] witnessGeometryChecked (by decide))
      cell181_check_indexed

/-- Closed-cover cell 182 for the fixed row-04 divisor, with 26 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 27, 14, 0, 0, 28]`; `cell182_check` verifies
its explicit-potential certificate. -/
def cell182 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 27, 14, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0,
      0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0]] }

private theorem cell182_check_indexed : cell182.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 0, 0, 4, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16], [], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19, 18, 0, 0, 0, 0, 10, 20], [21, 22, 23, 22, 0, 0, 0,
     0, 4, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 7, 17, 25, 0, 0, 26, 20]]
     = true := by
  decide +kernel

theorem cell182_check :
    cell182.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 15, 0, 27, 14, 0, 0, 28] witnessGeometryChecked (by decide))
      cell182_check_indexed

/-- Closed-cover cell 183 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 21, 9, 0, 0, 22]`; `cell183_check` verifies
its explicit-potential certificate. -/
def cell183 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 21, 9, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

private theorem cell183_check_indexed : cell183.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0,
     0, 0, 0, 11, 19], [0, 0, 13, 1, 20, 15, 0, 0, 4, 21], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     22, 23, 0, 0, 0, 0, 0, 0, 11, 19]] = true := by
  decide +kernel

theorem cell183_check :
    cell183.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 21, 9, 0, 0, 22] witnessGeometryChecked (by decide))
      cell183_check_indexed

/-- Closed-cover cell 184 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 5, 9, 0, 0, 5]`; `cell184_check` verifies its
explicit-potential certificate. -/
def cell184 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 5, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell184_check_indexed : cell184.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 19, 20]] = true := by
  decide +kernel

theorem cell184_check :
    cell184.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 5, 9, 0, 0, 5] witnessGeometryChecked (by decide))
      cell184_check_indexed

/-- Closed-cover cell 185 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 26, 9, 0, 0, 5]`; `cell185_check` verifies
its explicit-potential certificate. -/
def cell185 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 26, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1]] }

private theorem cell185_check_indexed : cell185.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 0, 0, 10, 18, 23, 24]] = true := by
  decide +kernel

theorem cell185_check :
    cell185.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 26, 9, 0, 0, 5] witnessGeometryChecked (by decide))
      cell185_check_indexed

/-- Closed-cover cell 186 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 25, 9, 0, 0, 6]`; `cell186_check` verifies
its explicit-potential certificate. -/
def cell186 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 25, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0]] }

private theorem cell186_check_indexed : cell186.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 0, 0, 20, 21], [0, 0, 13, 1, 22, 15, 0, 0, 4, 23], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 18, 19, 0, 0, 10, 21]] = true := by
  decide +kernel

theorem cell186_check :
    cell186.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 25, 9, 0, 0, 6] witnessGeometryChecked (by decide))
      cell186_check_indexed

/-- Closed-cover cell 187 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 9, 0, 0, 28]`; `cell187_check` verifies
its explicit-potential certificate. -/
def cell187 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 9, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

private theorem cell187_check_indexed : cell187.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 23, 7, 17, 24, 0, 0, 25, 20]] = true := by
  decide +kernel

theorem cell187_check :
    cell187.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 9, 0, 0, 28] witnessGeometryChecked (by decide))
      cell187_check_indexed

/-- Closed-cover cell 188 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 9, 0, 0, 7]`; `cell188_check` verifies
its explicit-potential certificate. -/
def cell188 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 9, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

private theorem cell188_check_indexed : cell188.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 23, 24, 25, 24, 0, 0, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell188_check :
    cell188.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 9, 0, 0, 7] witnessGeometryChecked (by decide))
      cell188_check_indexed

/-- Closed-cover cell 189 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 23, 9, 0, 0, 24]`; `cell189_check` verifies
its explicit-potential certificate. -/
def cell189 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 23, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell189_check_indexed : cell189.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 0, 0, 10, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 19, 23, 24]] = true := by
  decide +kernel

theorem cell189_check :
    cell189.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 23, 9, 0, 0, 24] witnessGeometryChecked (by decide))
      cell189_check_indexed

/-- Closed-cover cell 190 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 29, 9, 0, 0, 24]`; `cell190_check` verifies
its explicit-potential certificate. -/
def cell190 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 29, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1,
      1], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell190_check_indexed : cell190.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 18, 19, 18, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 25]] = true := by
  decide +kernel

theorem cell190_check :
    cell190.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 29, 9, 0, 0, 24] witnessGeometryChecked (by decide))
      cell190_check_indexed

/-- Closed-cover cell 191 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 30, 9, 0, 0, 24]`; `cell191_check` verifies
its explicit-potential certificate. -/
def cell191 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 30, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

private theorem cell191_check_indexed : cell191.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 18, 19, 11, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 19]] = true := by
  decide +kernel

theorem cell191_check :
    cell191.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 30, 9, 0, 0, 24] witnessGeometryChecked (by decide))
      cell191_check_indexed

/-- Closed-cover cell 192 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 21, 10, 0, 0, 22]`; `cell192_check` verifies
its explicit-potential certificate. -/
def cell192 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 21, 10, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0,
      -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
      1]] }

private theorem cell192_check_indexed : cell192.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0,
     0, 0, 0, 11, 19], [0, 0, 13, 1, 0, 0, 20, 21, 20, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     23, 24, 0, 0, 0, 0, 0, 0, 11, 19]] = true := by
  decide +kernel

theorem cell192_check :
    cell192.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 21, 10, 0, 0, 22] witnessGeometryChecked (by decide))
      cell192_check_indexed

/-- Closed-cover cell 193 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 26, 9, 0, 0, 24]`; `cell193_check` verifies
its explicit-potential certificate. -/
def cell193 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 26, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

private theorem cell193_check_indexed : cell193.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17,
     7, 0, 0, 0, 0, 10, 18, 19, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 7, 0, 0, 23, 24, 23, 25]] = true := by
  decide +kernel

theorem cell193_check :
    cell193.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 26, 9, 0, 0, 24] witnessGeometryChecked (by decide))
      cell193_check_indexed

/-- Closed-cover cell 194 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 27, 9, 0, 0, 6]`; `cell194_check` verifies
its explicit-potential certificate. -/
def cell194 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 27, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1],
      aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
      aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

private theorem cell194_check_indexed : cell194.certificate.checkClosedRows 4
    [[], [0, 0, 13, 1, 0, 0, 14, 15, 14, 16], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
     18, 0, 0, 0, 0, 10, 20], [0, 0, 13, 1, 21, 15, 0, 0, 4, 22], [], [], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 23, 7, 17, 24, 0, 0, 10, 20]] = true := by
  decide +kernel

theorem cell194_check :
    cell194.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row04Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 17, 0, 27, 9, 0, 0, 6] witnessGeometryChecked (by decide))
      cell194_check_indexed

/-- The ordered row-04 closed-cover cell block with global indices 98 through 194, used when
assembling the full 195-cell cover. -/
def chunk : List (CoordinateCell row04Core) :=
  [cell98, cell99, cell100, cell101, cell102, cell103, cell104, cell105, cell106, cell107, cell108,
  cell109, cell110, cell111, cell112, cell113, cell114, cell115, cell116, cell117, cell118, cell119,
  cell120, cell121, cell122, cell123, cell124, cell125, cell126, cell127, cell128, cell129, cell130,
  cell131, cell132, cell133, cell134, cell135, cell136, cell137, cell138, cell139, cell140, cell141,
  cell142, cell143, cell144, cell145, cell146, cell147, cell148, cell149, cell150, cell151, cell152,
  cell153, cell154, cell155, cell156, cell157, cell158, cell159, cell160, cell161, cell162, cell163,
  cell164, cell165, cell166, cell167, cell168, cell169, cell170, cell171, cell172, cell173, cell174,
  cell175, cell176, cell177, cell178, cell179, cell180, cell181, cell182, cell183, cell184, cell185,
  cell186, cell187, cell188, cell189, cell190, cell191, cell192, cell193, cell194]

theorem chunk_check :
    chunk.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [chunk, cell98_check, cell99_check, cell100_check, cell101_check, cell102_check,
    cell103_check, cell104_check, cell105_check, cell106_check, cell107_check, cell108_check,
    cell109_check, cell110_check, cell111_check, cell112_check, cell113_check, cell114_check,
    cell115_check, cell116_check, cell117_check, cell118_check, cell119_check, cell120_check,
    cell121_check, cell122_check, cell123_check, cell124_check, cell125_check, cell126_check,
    cell127_check, cell128_check, cell129_check, cell130_check, cell131_check, cell132_check,
    cell133_check, cell134_check, cell135_check, cell136_check, cell137_check, cell138_check,
    cell139_check, cell140_check, cell141_check, cell142_check, cell143_check, cell144_check,
    cell145_check, cell146_check, cell147_check, cell148_check, cell149_check, cell150_check,
    cell151_check, cell152_check, cell153_check, cell154_check, cell155_check, cell156_check,
    cell157_check, cell158_check, cell159_check, cell160_check, cell161_check, cell162_check,
    cell163_check, cell164_check, cell165_check, cell166_check, cell167_check, cell168_check,
    cell169_check, cell170_check, cell171_check, cell172_check, cell173_check, cell174_check,
    cell175_check, cell176_check, cell177_check, cell178_check, cell179_check, cell180_check,
    cell181_check, cell182_check, cell183_check, cell184_check, cell185_check, cell186_check,
    cell187_check, cell188_check, cell189_check, cell190_check, cell191_check, cell192_check,
    cell193_check, cell194_check]

end AtanasovRanganathan.GenusFiveRow04CoverCells1
