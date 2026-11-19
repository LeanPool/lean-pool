/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


import LeanPool.BrillNoetherGraphs.LowGenus.CompactCellTreeLookup
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IndexedClosedCheck
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverData
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks0
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks1
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks2
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks3
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks4
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks5
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks6
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks7
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks8
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks9
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow03FixedCoverChecks10

/-! **Independent generated check.** The main row-03 proof is now
`GenusFiveTwoPoleClosed.row03_closedConstruction`; this module preserves
an additional exact replay.

Generated exact replay of the fixed AR row-03 divisor.
`cells_check` and `tree_check` replay every arithmetic obligation in the kernel.

Passive definitions are re-exported from the data module. Bounded kernel-replay batches
limit cumulative checking cost; the wrappers retain the original auxiliary declarations. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

/-- Witness indices used at each anchor by the generated closed-cover cells. -/
private def witnessGeometryRows : List (List ℕ) :=
  [[0], [0], [1, 5, 9, 10, 15, 16, 17, 20, 22, 23, 24, 29, 30, 31], [2, 6, 8, 13, 32, 34, 35, 38,
   39, 44, 46, 47], [0], [0], [3, 7, 11, 12, 14, 16, 18, 19, 21, 25, 26, 27, 28], [4, 33, 36, 37,
   40, 41, 42, 43, 45, 48, 49]]

/-- Every used anchor/witness pair passes the original slope and endpoint checks. -/
private theorem witnessGeometryChecked :
    CertificateData.checkWitnessPool row03Core rowDivisor witnesses defaultWitness
      witnessGeometryRows = true := by
  decide +kernel

private theorem cell0_check_indexed : cell0.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 13, 14, 15], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 8, 16, 15, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 14]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell0_check_indexed

theorem cell0_check :
    cell0.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 1, 2, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell0_check_indexed

private theorem cell1_check_indexed : cell1.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell1_check_indexed

theorem cell1_check :
    cell1.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 5, 6, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell1_check_indexed

private theorem cell2_check_indexed : cell2.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 18, 4, 0, 0, 0, 0, 0,
     0, 9, 19, 4, 20], [], [], [21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell2_check_indexed

theorem cell2_check :
    cell2.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 5, 8, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell2_check_indexed

private theorem cell3_check_indexed : cell3.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell3_check_indexed

theorem cell3_check :
    cell3.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 9, 6, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell3_check_indexed

private theorem cell4_check_indexed : cell4.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 4, 0, 0, 0, 0, 0,
     0, 9, 19, 4, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell4_check_indexed

theorem cell4_check :
    cell4.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 9, 8, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell4_check_indexed

private theorem cell5_check_indexed : cell5.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16, 21,
     22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell5_check_indexed

theorem cell5_check :
    cell5.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 6, 0, 0, 11, 4] witnessGeometryChecked (by decide))
      cell5_check_indexed

private theorem cell6_check_indexed : cell6.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell6_check_indexed

theorem cell6_check :
    cell6.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 8, 0, 0, 11, 4] witnessGeometryChecked (by decide))
      cell6_check_indexed

private theorem cell7_check_indexed : cell7.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21,
     0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell7_check_indexed

theorem cell7_check :
    cell7.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 6, 0, 0, 12, 4] witnessGeometryChecked (by decide))
      cell7_check_indexed

private theorem cell8_check_indexed : cell8.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell8_check_indexed

theorem cell8_check :
    cell8.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 8, 0, 0, 12, 4] witnessGeometryChecked (by decide))
      cell8_check_indexed

private theorem cell9_check_indexed : cell9.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0,
     0, 9, 19, 3, 20], [], [], [21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell9_check_indexed

theorem cell9_check :
    cell9.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 5, 13, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell9_check_indexed

private theorem cell10_check_indexed : cell10.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0,
     0, 9, 19, 3, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell10_check_indexed

theorem cell10_check :
    cell10.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 9, 13, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell10_check_indexed

private theorem cell11_check_indexed : cell11.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell11_check_indexed

theorem cell11_check :
    cell11.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 13, 0, 0, 14, 4] witnessGeometryChecked (by decide))
      cell11_check_indexed

private theorem cell12_check_indexed : cell12.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell12_check_indexed

theorem cell12_check :
    cell12.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 13, 0, 0, 11, 4] witnessGeometryChecked (by decide))
      cell12_check_indexed

private theorem cell13_check_indexed : cell13.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell13_check_indexed

theorem cell13_check :
    cell13.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 13, 0, 0, 12, 4] witnessGeometryChecked (by decide))
      cell13_check_indexed

private theorem cell14_check_indexed : cell14.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [14, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell14_check_indexed

theorem cell14_check :
    cell14.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 15, 6, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell14_check_indexed

private theorem cell15_check_indexed : cell15.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 4, 0, 0, 0, 0, 0,
     0, 9, 19, 4, 20], [], [], [14, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell15_check_indexed

theorem cell15_check :
    cell15.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 15, 8, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell15_check_indexed

private theorem cell16_check_indexed : cell16.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [20, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22,
     23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell16_check_indexed

theorem cell16_check :
    cell16.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 6, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell16_check_indexed

private theorem cell17_check_indexed : cell17.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [20, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0,
     0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell17_check_indexed

theorem cell17_check :
    cell17.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 8, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell17_check_indexed

private theorem cell18_check_indexed : cell18.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0,
     0, 9, 19, 3, 20], [], [], [14, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell18_check_indexed

theorem cell18_check :
    cell18.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 15, 13, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell18_check_indexed

private theorem cell19_check_indexed : cell19.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [20, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0,
     0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell19_check_indexed

theorem cell19_check :
    cell19.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 13, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell19_check_indexed

private theorem cell20_check_indexed : cell20.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0,
     0, 9, 19, 3, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell20_check_indexed

theorem cell20_check :
    cell20.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 16, 13, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell20_check_indexed

private theorem cell21_check_indexed : cell21.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 16, 21,
     22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell21_check_indexed

theorem cell21_check :
    cell21.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 6, 0, 0, 18, 4] witnessGeometryChecked (by decide))
      cell21_check_indexed

private theorem cell22_check_indexed : cell22.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell22_check_indexed

theorem cell22_check :
    cell22.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 13, 0, 0, 18, 4] witnessGeometryChecked (by decide))
      cell22_check_indexed

private theorem cell23_check_indexed : cell23.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16, 21,
     22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks0.cell23_check_indexed

theorem cell23_check :
    cell23.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 6, 0, 0, 16, 4] witnessGeometryChecked (by decide))
      cell23_check_indexed

private theorem cell24_check_indexed : cell24.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell24_check_indexed

theorem cell24_check :
    cell24.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 6, 0, 0, 14, 4] witnessGeometryChecked (by decide))
      cell24_check_indexed

private theorem cell25_check_indexed : cell25.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell25_check_indexed

theorem cell25_check :
    cell25.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 8, 0, 0, 18, 4] witnessGeometryChecked (by decide))
      cell25_check_indexed

private theorem cell26_check_indexed : cell26.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16,
     21, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell26_check_indexed

theorem cell26_check :
    cell26.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 8, 0, 0, 16, 4] witnessGeometryChecked (by decide))
      cell26_check_indexed

private theorem cell27_check_indexed : cell27.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell27_check_indexed

theorem cell27_check :
    cell27.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 8, 0, 0, 14, 4] witnessGeometryChecked (by decide))
      cell27_check_indexed

private theorem cell28_check_indexed : cell28.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21,
     0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell28_check_indexed

theorem cell28_check :
    cell28.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 6, 0, 0, 19, 4] witnessGeometryChecked (by decide))
      cell28_check_indexed

private theorem cell29_check_indexed : cell29.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell29_check_indexed

theorem cell29_check :
    cell29.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 8, 0, 0, 19, 4] witnessGeometryChecked (by decide))
      cell29_check_indexed

private theorem cell30_check_indexed : cell30.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell30_check_indexed

theorem cell30_check :
    cell30.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 13, 0, 0, 19, 4] witnessGeometryChecked (by decide))
      cell30_check_indexed

private theorem cell31_check_indexed : cell31.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 13, 14, 15, 16], [0,
     0, 0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [20, 19, 19, 21, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell31_check_indexed

theorem cell31_check :
    cell31.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 20, 6, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell31_check_indexed

private theorem cell32_check_indexed : cell32.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 18, 8, 8, 19, 0, 0, 0, 0, 9, 16], [], [], [20, 16, 16, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell32_check_indexed

theorem cell32_check :
    cell32.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 22, 6, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell32_check_indexed

private theorem cell33_check_indexed : cell33.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0,
     0, 0, 0, 18, 8, 8, 19, 0, 0, 0, 0, 9, 16], [], [], [20, 16, 16, 21, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell33_check_indexed

theorem cell33_check :
    cell33.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 23, 6, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell33_check_indexed

private theorem cell34_check_indexed : cell34.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 18, 8, 8, 19, 0, 0, 0, 0, 9, 16], [], [], [14, 16, 16, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell34_check_indexed

theorem cell34_check :
    cell34.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 24, 6, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell34_check_indexed

private theorem cell35_check_indexed : cell35.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 13, 14, 15, 16], [0,
     0, 0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [20, 18, 18, 21, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell35_check_indexed

theorem cell35_check :
    cell35.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 20, 8, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell35_check_indexed

private theorem cell36_check_indexed : cell36.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 18, 4, 0, 0, 0, 0, 0, 0, 9, 16, 4, 19], [], [], [20, 16, 16, 14, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell36_check_indexed

theorem cell36_check :
    cell36.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 22, 8, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell36_check_indexed

private theorem cell37_check_indexed : cell37.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0,
     0, 0, 0, 18, 4, 0, 0, 0, 0, 0, 0, 9, 16, 4, 19], [], [], [20, 16, 16, 21, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell37_check_indexed

theorem cell37_check :
    cell37.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 23, 8, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell37_check_indexed

private theorem cell38_check_indexed : cell38.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 18, 4, 0, 0, 0, 0, 0, 0, 9, 16, 4, 19], [], [], [14, 16, 16, 20, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell38_check_indexed

theorem cell38_check :
    cell38.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 24, 8, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell38_check_indexed

private theorem cell39_check_indexed : cell39.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell39_check_indexed

theorem cell39_check :
    cell39.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 6, 0, 0, 25, 4] witnessGeometryChecked (by decide))
      cell39_check_indexed

private theorem cell40_check_indexed : cell40.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell40_check_indexed

theorem cell40_check :
    cell40.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 8, 0, 0, 26, 4] witnessGeometryChecked (by decide))
      cell40_check_indexed

private theorem cell41_check_indexed : cell41.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell41_check_indexed

theorem cell41_check :
    cell41.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 8, 0, 0, 25, 4] witnessGeometryChecked (by decide))
      cell41_check_indexed

private theorem cell42_check_indexed : cell42.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 15, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 19, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell42_check_indexed

theorem cell42_check :
    cell42.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 6, 0, 0, 27, 4] witnessGeometryChecked (by decide))
      cell42_check_indexed

private theorem cell43_check_indexed : cell43.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell43_check_indexed

theorem cell43_check :
    cell43.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 8, 0, 0, 27, 4] witnessGeometryChecked (by decide))
      cell43_check_indexed

private theorem cell44_check_indexed : cell44.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 20, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell44_check_indexed

theorem cell44_check :
    cell44.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 6, 0, 0, 26, 4] witnessGeometryChecked (by decide))
      cell44_check_indexed

private theorem cell45_check_indexed : cell45.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 8, 8, 18, 0, 0, 0, 0, 9, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 20, 15, 20, 15, 1, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell45_check_indexed

theorem cell45_check :
    cell45.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 6, 0, 0, 28, 4] witnessGeometryChecked (by decide))
      cell45_check_indexed

private theorem cell46_check_indexed : cell46.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 17, 4, 0, 0, 0, 0, 0, 0, 9, 18, 4, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 20, 15, 20, 15, 1, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell46_check_indexed

theorem cell46_check :
    cell46.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 8, 0, 0, 28, 4] witnessGeometryChecked (by decide))
      cell46_check_indexed

private theorem cell47_check_indexed : cell47.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 13, 14, 15, 16], [0,
     0, 0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [20, 18, 18, 21, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 22], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks1.cell47_check_indexed

theorem cell47_check :
    cell47.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 20, 13, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell47_check_indexed

private theorem cell48_check_indexed : cell48.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 9, 16, 3, 19], [], [], [20, 16, 16, 14, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell48_check_indexed

theorem cell48_check :
    cell48.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 22, 13, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell48_check_indexed

private theorem cell49_check_indexed : cell49.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0,
     0, 0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 9, 16, 3, 19], [], [], [20, 16, 16, 21, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell49_check_indexed

theorem cell49_check :
    cell49.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 23, 13, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell49_check_indexed

private theorem cell50_check_indexed : cell50.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 9, 16, 3, 19], [], [], [14, 16, 16, 20, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell50_check_indexed

theorem cell50_check :
    cell50.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 24, 13, 0, 0, 21, 4] witnessGeometryChecked (by decide))
      cell50_check_indexed

private theorem cell51_check_indexed : cell51.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 20, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell51_check_indexed

theorem cell51_check :
    cell51.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 13, 0, 0, 26, 4] witnessGeometryChecked (by decide))
      cell51_check_indexed

private theorem cell52_check_indexed : cell52.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell52_check_indexed

theorem cell52_check :
    cell52.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 13, 0, 0, 25, 4] witnessGeometryChecked (by decide))
      cell52_check_indexed

private theorem cell53_check_indexed : cell53.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 15,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell53_check_indexed

theorem cell53_check :
    cell53.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 13, 0, 0, 27, 4] witnessGeometryChecked (by decide))
      cell53_check_indexed

private theorem cell54_check_indexed : cell54.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16], [0, 0,
     0, 0, 0, 0, 3, 17, 0, 0, 0, 0, 9, 18, 3, 19], [], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 20, 15, 20, 15, 1, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell54_check_indexed

theorem cell54_check :
    cell54.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 17, 13, 0, 0, 28, 4] witnessGeometryChecked (by decide))
      cell54_check_indexed

private theorem cell55_check_indexed : cell55.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 13, 14, 15], [0, 0, 0, 0, 16, 8, 8, 17,
     0, 0, 0, 0, 9, 14], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 14]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell55_check_indexed

theorem cell55_check :
    cell55.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 1, 6, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell55_check_indexed

private theorem cell56_check_indexed : cell56.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [21, 12, 12, 14, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell56_check_indexed

theorem cell56_check :
    cell56.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 16, 6, 0, 0, 7, 4] witnessGeometryChecked (by decide))
      cell56_check_indexed

private theorem cell57_check_indexed : cell57.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 18, 8, 8, 19, 0, 0, 0,
     0, 9, 20], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 9, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell57_check_indexed

theorem cell57_check :
    cell57.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 16, 6, 0, 0, 16, 4] witnessGeometryChecked (by decide))
      cell57_check_indexed

private theorem cell58_check_indexed : cell58.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 13, 14, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 9, 14, 4, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 14]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell58_check_indexed

theorem cell58_check :
    cell58.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 1, 8, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell58_check_indexed

private theorem cell59_check_indexed : cell59.certificate.checkClosedRows 4
    [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 13, 14, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 9, 14, 3, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 14]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell59_check_indexed

theorem cell59_check :
    cell59.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 1, 13, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell59_check_indexed

private theorem cell60_check_indexed : cell60.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0,
     0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 9, 16, 3, 19], [], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21,
     22, 23], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 16]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell60_check_indexed

theorem cell60_check :
    cell60.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 22, 13, 0, 0, 11, 4] witnessGeometryChecked (by decide))
      cell60_check_indexed

private theorem cell61_check_indexed : cell61.certificate.checkClosedRows 4
    [[], [], [13, 14, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8,
     18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 19], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell61_check_indexed

theorem cell61_check :
    cell61.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 5, 2, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell61_check_indexed

private theorem cell62_check_indexed : cell62.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 8, 16, 15, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell62_check_indexed

theorem cell62_check :
    cell62.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 2, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell62_check_indexed

private theorem cell63_check_indexed : cell63.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 8, 16, 15, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell63_check_indexed

theorem cell63_check :
    cell63.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 2, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell63_check_indexed

private theorem cell64_check_indexed : cell64.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8,
     18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 19], [0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 9, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell64_check_indexed

theorem cell64_check :
    cell64.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 9, 2, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell64_check_indexed

private theorem cell65_check_indexed : cell65.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 2, 16], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 8, 17, 18, 19], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 7, 18], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 19]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell65_check_indexed

theorem cell65_check :
    cell65.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 10, 2, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell65_check_indexed

private theorem cell66_check_indexed : cell66.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 8, 16, 15, 17], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 17]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell66_check_indexed

theorem cell66_check :
    cell66.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 2, 0, 0, 3, 4] witnessGeometryChecked (by decide))
      cell66_check_indexed

private theorem cell67_check_indexed : cell67.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell67_check_indexed

theorem cell67_check :
    cell67.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 32, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell67_check_indexed

private theorem cell68_check_indexed : cell68.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell68_check_indexed

theorem cell68_check :
    cell68.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 32, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell68_check_indexed

private theorem cell69_check_indexed : cell69.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 17, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell69_check_indexed

theorem cell69_check :
    cell69.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 34, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell69_check_indexed

private theorem cell70_check_indexed : cell70.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell70_check_indexed

theorem cell70_check :
    cell70.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 35, 0, 0, 3, 36] witnessGeometryChecked (by decide))
      cell70_check_indexed

private theorem cell71_check_indexed : cell71.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  as_aux_lemma =>
    exact ReplayChecks2.cell71_check_indexed

theorem cell71_check :
    cell71.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 35, 0, 0, 3, 37] witnessGeometryChecked (by decide))
      cell71_check_indexed

private theorem cell72_check_indexed : cell72.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 17, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell72_check_indexed

theorem cell72_check :
    cell72.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 34, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell72_check_indexed

private theorem cell73_check_indexed : cell73.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell73_check_indexed

theorem cell73_check :
    cell73.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 35, 0, 0, 3, 36] witnessGeometryChecked (by decide))
      cell73_check_indexed

private theorem cell74_check_indexed : cell74.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell74_check_indexed

theorem cell74_check :
    cell74.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 35, 0, 0, 3, 37] witnessGeometryChecked (by decide))
      cell74_check_indexed

private theorem cell75_check_indexed : cell75.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 17, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell75_check_indexed

theorem cell75_check :
    cell75.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 38, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell75_check_indexed

private theorem cell76_check_indexed : cell76.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 17, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell76_check_indexed

theorem cell76_check :
    cell76.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 38, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell76_check_indexed

private theorem cell77_check_indexed : cell77.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell77_check_indexed

theorem cell77_check :
    cell77.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 39, 0, 0, 3, 40] witnessGeometryChecked (by decide))
      cell77_check_indexed

private theorem cell78_check_indexed : cell78.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell78_check_indexed

theorem cell78_check :
    cell78.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 35, 0, 0, 3, 41] witnessGeometryChecked (by decide))
      cell78_check_indexed

private theorem cell79_check_indexed : cell79.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell79_check_indexed

theorem cell79_check :
    cell79.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 35, 0, 0, 3, 42] witnessGeometryChecked (by decide))
      cell79_check_indexed

private theorem cell80_check_indexed : cell80.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell80_check_indexed

theorem cell80_check :
    cell80.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 39, 0, 0, 3, 43] witnessGeometryChecked (by decide))
      cell80_check_indexed

private theorem cell81_check_indexed : cell81.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell81_check_indexed

theorem cell81_check :
    cell81.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 39, 0, 0, 3, 40] witnessGeometryChecked (by decide))
      cell81_check_indexed

private theorem cell82_check_indexed : cell82.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell82_check_indexed

theorem cell82_check :
    cell82.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 35, 0, 0, 3, 42] witnessGeometryChecked (by decide))
      cell82_check_indexed

private theorem cell83_check_indexed : cell83.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell83_check_indexed

theorem cell83_check :
    cell83.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 39, 0, 0, 3, 43] witnessGeometryChecked (by decide))
      cell83_check_indexed

private theorem cell84_check_indexed : cell84.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell84_check_indexed

theorem cell84_check :
    cell84.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 32, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell84_check_indexed

private theorem cell85_check_indexed : cell85.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 21, 12, 12, 17, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell85_check_indexed

theorem cell85_check :
    cell85.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 34, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell85_check_indexed

private theorem cell86_check_indexed : cell86.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell86_check_indexed

theorem cell86_check :
    cell86.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 35, 0, 0, 3, 36] witnessGeometryChecked (by decide))
      cell86_check_indexed

private theorem cell87_check_indexed : cell87.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell87_check_indexed

theorem cell87_check :
    cell87.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 35, 0, 0, 3, 37] witnessGeometryChecked (by decide))
      cell87_check_indexed

private theorem cell88_check_indexed : cell88.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 19, 20], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     7, 15], [0, 0, 0, 0, 17, 12, 12, 21, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell88_check_indexed

theorem cell88_check :
    cell88.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 38, 0, 0, 3, 33] witnessGeometryChecked (by decide))
      cell88_check_indexed

private theorem cell89_check_indexed : cell89.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 19, 21, 22]]
     = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell89_check_indexed

theorem cell89_check :
    cell89.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 39, 0, 0, 3, 40] witnessGeometryChecked (by decide))
      cell89_check_indexed

private theorem cell90_check_indexed : cell90.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell90_check_indexed

theorem cell90_check :
    cell90.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 35, 0, 0, 3, 42] witnessGeometryChecked (by decide))
      cell90_check_indexed

private theorem cell91_check_indexed : cell91.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0,
     22, 23]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell91_check_indexed

theorem cell91_check :
    cell91.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 39, 0, 0, 3, 43] witnessGeometryChecked (by decide))
      cell91_check_indexed

private theorem cell92_check_indexed : cell92.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell92_check_indexed

theorem cell92_check :
    cell92.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 44, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell92_check_indexed

private theorem cell93_check_indexed : cell93.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell93_check_indexed

theorem cell93_check :
    cell93.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 44, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell93_check_indexed

private theorem cell94_check_indexed : cell94.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell94_check_indexed

theorem cell94_check :
    cell94.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 46, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell94_check_indexed

private theorem cell95_check_indexed : cell95.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks3.cell95_check_indexed

theorem cell95_check :
    cell95.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 46, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell95_check_indexed

private theorem cell96_check_indexed : cell96.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell96_check_indexed

theorem cell96_check :
    cell96.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 35, 0, 0, 3, 41] witnessGeometryChecked (by decide))
      cell96_check_indexed

private theorem cell97_check_indexed : cell97.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 17, 15, 15, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell97_check_indexed

theorem cell97_check :
    cell97.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 47, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell97_check_indexed

private theorem cell98_check_indexed : cell98.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 17, 15, 15, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell98_check_indexed

theorem cell98_check :
    cell98.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 47, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell98_check_indexed

private theorem cell99_check_indexed : cell99.certificate.checkClosedRows 4
    [[], [], [13, 6, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell99_check_indexed

theorem cell99_check :
    cell99.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 29, 39, 0, 0, 3, 48] witnessGeometryChecked (by decide))
      cell99_check_indexed

private theorem cell100_check_indexed : cell100.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell100_check_indexed

theorem cell100_check :
    cell100.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 39, 0, 0, 3, 48] witnessGeometryChecked (by decide))
      cell100_check_indexed

private theorem cell101_check_indexed : cell101.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 17, 17,
     18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell101_check_indexed

theorem cell101_check :
    cell101.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 44, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell101_check_indexed

private theorem cell102_check_indexed : cell102.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 17, 15, 15, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell102_check_indexed

theorem cell102_check :
    cell102.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 47, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell102_check_indexed

private theorem cell103_check_indexed : cell103.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell103_check_indexed

theorem cell103_check :
    cell103.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 39, 0, 0, 3, 48] witnessGeometryChecked (by decide))
      cell103_check_indexed

private theorem cell104_check_indexed : cell104.certificate.checkClosedRows 4
    [[], [], [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell104_check_indexed

theorem cell104_check :
    cell104.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 31, 39, 0, 0, 3, 49] witnessGeometryChecked (by decide))
      cell104_check_indexed

private theorem cell105_check_indexed : cell105.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20, 18, 0, 0, 0, 0, 0, 0,
     21, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell105_check_indexed

theorem cell105_check :
    cell105.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 35, 0, 0, 3, 41] witnessGeometryChecked (by decide))
      cell105_check_indexed

private theorem cell106_check_indexed : cell106.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 16, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 0, 0, 19, 15], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 20, 15, 15, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 19, 15]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell106_check_indexed

theorem cell106_check :
    cell106.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 46, 0, 0, 3, 45] witnessGeometryChecked (by decide))
      cell106_check_indexed

private theorem cell107_check_indexed : cell107.certificate.checkClosedRows 4
    [[], [], [0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 1, 14, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16,
     0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0, 19, 3], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 7, 15], [0, 0, 0, 0, 0, 0, 3, 16, 0, 0, 0, 0, 0, 0, 0, 0, 17, 18, 0, 0, 0, 0,
     19, 20]] = true := by
  as_aux_lemma =>
    exact ReplayChecks4.cell107_check_indexed

theorem cell107_check :
    cell107.certificate.checkClosed 4 = true := by
  as_aux_lemma =>
    exact CertificateData.checkClosedRows_sound _ _ _
      (CertificateData.checkWitnessSelection row03Core rowDivisor witnesses defaultWitness
        witnessGeometryRows [0, 0, 30, 39, 0, 0, 3, 49] witnessGeometryChecked (by decide))
      cell107_check_indexed

theorem splitForm0 : splitForms.getD 0 0 = aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm1 : splitForms.getD 1 0 = aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm2 : splitForms.getD 2 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm3 : splitForms.getD 3 0 = aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm4 : splitForms.getD 4 0 = aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1] := by rfl

theorem splitForm5 : splitForms.getD 5 0 = aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm6 : splitForms.getD 6 0 = aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm7 : splitForms.getD 7 0 = aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm8 : splitForms.getD 8 0 = aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm9 : splitForms.getD 9 0 = aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm10 : splitForms.getD 10 0 = aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm11 : splitForms.getD 11 0 = aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm12 : splitForms.getD 12 0 = aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm13 : splitForms.getD 13 0 = aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm14 : splitForms.getD 14 0 = aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm15 : splitForms.getD 15 0 = aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm16 : splitForms.getD 16 0 = aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm17 : splitForms.getD 17 0 = aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm18 : splitForms.getD 18 0 = aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm19 : splitForms.getD 19 0 = aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm20 : splitForms.getD 20 0 = aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm21 : splitForms.getD 21 0 = aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm22 :
    splitForms.getD 22 0 = aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm23 : splitForms.getD 23 0 = aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm24 : splitForms.getD 24 0 = aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm25 : splitForms.getD 25 0 = aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm26 : splitForms.getD 26 0 = aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm27 : splitForms.getD 27 0 = aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm28 : splitForms.getD 28 0 = aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1] := by rfl

theorem splitForm29 : splitForms.getD 29 0 = aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1] := by rfl

theorem splitForm30 : splitForms.getD 30 0 = aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1] := by rfl

theorem splitForm31 : splitForms.getD 31 0 = aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm32 : splitForms.getD 32 0 = aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1] := by rfl

theorem splitForm33 : splitForms.getD 33 0 = aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0] := by rfl

theorem splitForm34 : splitForms.getD 34 0 = aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0] := by rfl

theorem splitForm35 : splitForms.getD 35 0 = aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm36 : splitForms.getD 36 0 = aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm37 : splitForms.getD 37 0 = aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0] := by rfl

theorem splitForm38 : splitForms.getD 38 0 = aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1] := by rfl

theorem splitForm39 : splitForms.getD 39 0 = aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1] := by rfl

theorem splitForm40 : splitForms.getD 40 0 = aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm41 : splitForms.getD 41 0 = aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm42 : splitForms.getD 42 0 = aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm43 : splitForms.getD 43 0 = aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm44 :
    splitForms.getD 44 0 = aff [0, -1, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm45 : splitForms.getD 45 0 = aff [0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0] := by rfl

theorem splitForm46 : splitForms.getD 46 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0] := by rfl

theorem splitForm47 : splitForms.getD 47 0 = aff [0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm48 : splitForms.getD 48 0 = aff [0, -1, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm49 : splitForms.getD 49 0 = aff [0, 0, 1, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm50 : splitForms.getD 50 0 = aff [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm51 : splitForms.getD 51 0 = aff [0, 0, 1, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm52 : splitForms.getD 52 0 = aff [0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm53 : splitForms.getD 53 0 = aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm54 : splitForms.getD 54 0 = aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1] := by rfl

theorem splitForm55 : splitForms.getD 55 0 = aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm56 : splitForms.getD 56 0 = aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm57 : splitForms.getD 57 0 = aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1] := by rfl

theorem splitForm58 : splitForms.getD 58 0 = aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm59 :
    splitForms.getD 59 0 = aff [0, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 0, 0] := by rfl

theorem splitForm60 : splitForms.getD 60 0 = aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1] := by rfl

theorem splitForm61 : splitForms.getD 61 0 = aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm62 : splitForms.getD 62 0 = aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm63 : splitForms.getD 63 0 = aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1] := by rfl

theorem splitForm64 :
    splitForms.getD 64 0 = aff [0, 0, 0, -1, 0, 0, 0, -1, -1, 1, 0, 0, 0] := by rfl

theorem splitForm65 : splitForms.getD 65 0 = aff [0, 0, 0, 0, 1, 0, 0, 1, 1, -1, 0, 0, 0] := by rfl

theorem splitForm66 : splitForms.getD 66 0 = aff [0, 0, 0, 0, -1, 0, 0, -1, 1, 1, 0, 0, 0] := by rfl

theorem splitForm67 : splitForms.getD 67 0 = aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm68 : splitForms.getD 68 0 = aff [0, 0, 0, -1, 0, 0, 0, -1, 1, 1, 0, 0, 0] := by rfl

private theorem treePart0_check_chunked :
    treePart0.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart0_check_chunked

theorem treePart0_check :
    treePart0.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart0_check_chunked

private theorem treePart1_check_chunked :
    treePart1.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0,
      0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true
      := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart1_check_chunked

theorem treePart1_check :
    treePart1.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0,
      0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true
      := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart1_check_chunked

private theorem treePart2_check_chunked :
    treePart2.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0,
      0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart2_check_chunked

theorem treePart2_check :
    treePart2.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0,
      0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart2_check_chunked

private theorem treePart3_check_chunked :
    treePart3.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart3_check_chunked

theorem treePart3_check :
    treePart3.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart3_check_chunked

private theorem treePart4_check_chunked :
    treePart4.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart4_check_chunked

theorem treePart4_check :
    treePart4.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart4_check_chunked

private theorem treePart5_check_chunked :
    treePart5.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart5_check_chunked

theorem treePart5_check :
    treePart5.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart5_check_chunked

private theorem treePart6_check_chunked :
    treePart6.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart6_check_chunked

theorem treePart6_check :
    treePart6.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart6_check_chunked

private theorem treePart7_check_chunked :
    treePart7.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart7_check_chunked

theorem treePart7_check :
    treePart7.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart7_check_chunked

private theorem treePart8_check_chunked :
    treePart8.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart8_check_chunked

theorem treePart8_check :
    treePart8.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart8_check_chunked

private theorem treePart9_check_chunked :
    treePart9.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart9_check_chunked

theorem treePart9_check :
    treePart9.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart9_check_chunked

private theorem treePart10_check_chunked :
    treePart10.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart10_check_chunked

theorem treePart10_check :
    treePart10.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart10_check_chunked

private theorem treePart11_check_chunked :
    treePart11.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks4.treePart11_check_chunked

theorem treePart11_check :
    treePart11.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart11_check_chunked

private theorem treePart12_check_chunked :
    treePart12.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]])
      ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart12_check_chunked

theorem treePart12_check :
    treePart12.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]])
      ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart12_check_chunked

private theorem treePart13_check_chunked :
    treePart13.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart13_check_chunked

theorem treePart13_check :
    treePart13.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart13_check_chunked

private theorem treePart14_check_chunked :
    treePart14.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart14_check_chunked

theorem treePart14_check :
    treePart14.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart14_check_chunked

private theorem treePart15_check_chunked :
    treePart15.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart15_check_chunked

theorem treePart15_check :
    treePart15.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart15_check_chunked

private theorem treePart16_check_chunked :
    treePart16.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart16_check_chunked

theorem treePart16_check :
    treePart16.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart16_check_chunked

private theorem treePart17_check_chunked :
    treePart17.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart17_check_chunked

theorem treePart17_check :
    treePart17.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart17_check_chunked

private theorem treePart18_check_chunked :
    treePart18.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart18_check_chunked

theorem treePart18_check :
    treePart18.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0,
      0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart18_check_chunked

private theorem treePart19_check_chunked :
    treePart19.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart19_check_chunked

theorem treePart19_check :
    treePart19.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart19_check_chunked

private theorem treePart20_check_chunked :
    treePart20.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0,
      1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart20_check_chunked

theorem treePart20_check :
    treePart20.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0,
      1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart20_check_chunked

private theorem treePart21_check_chunked :
    treePart21.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0,
      1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0,
      -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart21_check_chunked

theorem treePart21_check :
    treePart21.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0,
      1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0,
      -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart21_check_chunked

private theorem treePart22_check_chunked :
    treePart22.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart22_check_chunked

theorem treePart22_check :
    treePart22.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart22_check_chunked

private theorem treePart23_check_chunked :
    treePart23.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart23_check_chunked

theorem treePart23_check :
    treePart23.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart23_check_chunked

private theorem treePart24_check_chunked :
    treePart24.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks5.treePart24_check_chunked

theorem treePart24_check :
    treePart24.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart24_check_chunked

private theorem treePart25_check_chunked :
    treePart25.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart25_check_chunked

theorem treePart25_check :
    treePart25.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart25_check_chunked

private theorem treePart26_check_chunked :
    treePart26.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart26_check_chunked

theorem treePart26_check :
    treePart26.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart26_check_chunked

private theorem treePart27_check_chunked :
    treePart27.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart27_check_chunked

theorem treePart27_check :
    treePart27.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart27_check_chunked

private theorem treePart28_check_chunked :
    treePart28.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart28_check_chunked

theorem treePart28_check :
    treePart28.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart28_check_chunked

private theorem treePart29_check_chunked :
    treePart29.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart29_check_chunked

theorem treePart29_check :
    treePart29.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart29_check_chunked

private theorem treePart30_check_chunked :
    treePart30.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart30_check_chunked

theorem treePart30_check :
    treePart30.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart30_check_chunked

private theorem treePart31_check_chunked :
    treePart31.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart31_check_chunked

theorem treePart31_check :
    treePart31.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart31_check_chunked

private theorem treePart32_check_chunked :
    treePart32.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart32_check_chunked

theorem treePart32_check :
    treePart32.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart32_check_chunked

private theorem treePart33_check_chunked :
    treePart33.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart33_check_chunked

theorem treePart33_check :
    treePart33.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart33_check_chunked

private theorem treePart34_check_chunked :
    treePart34.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart34_check_chunked

theorem treePart34_check :
    treePart34.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart34_check_chunked

private theorem treePart35_check_chunked :
    treePart35.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks5.treePart35_check_chunked

theorem treePart35_check :
    treePart35.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart35_check_chunked

private theorem treePart36_check_chunked :
    treePart36.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart36_check_chunked

theorem treePart36_check :
    treePart36.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart36_check_chunked

private theorem treePart37_check_chunked :
    treePart37.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart37_check_chunked

theorem treePart37_check :
    treePart37.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1,
      0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart37_check_chunked

private theorem treePart38_check_chunked :
    treePart38.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart38_check_chunked

theorem treePart38_check :
    treePart38.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart38_check_chunked

private theorem treePart39_check_chunked :
    treePart39.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart39_check_chunked

theorem treePart39_check :
    treePart39.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart39_check_chunked

private theorem treePart40_check_chunked :
    treePart40.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart40_check_chunked

theorem treePart40_check :
    treePart40.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff
      [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart40_check_chunked

private theorem treePart41_check_chunked :
    treePart41.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0,
      0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart41_check_chunked

theorem treePart41_check :
    treePart41.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0,
      0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart41_check_chunked

private theorem treePart42_check_chunked :
    treePart42.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart42_check_chunked

theorem treePart42_check :
    treePart42.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart42_check_chunked

private theorem treePart43_check_chunked :
    treePart43.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart43_check_chunked

theorem treePart43_check :
    treePart43.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])])
      ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart43_check_chunked

private theorem treePart44_check_chunked :
    treePart44.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks6.treePart44_check_chunked

theorem treePart44_check :
    treePart44.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart44_check_chunked

private theorem treePart45_check_chunked :
    treePart45.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart45_check_chunked

theorem treePart45_check :
    treePart45.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart45_check_chunked

private theorem treePart46_check_chunked :
    treePart46.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart46_check_chunked

theorem treePart46_check :
    treePart46.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart46_check_chunked

private theorem treePart47_check_chunked :
    treePart47.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0,
      0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart47_check_chunked

theorem treePart47_check :
    treePart47.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0,
      0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart47_check_chunked

private theorem treePart48_check_chunked :
    treePart48.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart48_check_chunked

theorem treePart48_check :
    treePart48.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart48_check_chunked

private theorem treePart49_check_chunked :
    treePart49.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart49_check_chunked

theorem treePart49_check :
    treePart49.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart49_check_chunked

private theorem treePart50_check_chunked :
    treePart50.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart50_check_chunked

theorem treePart50_check :
    treePart50.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart50_check_chunked

private theorem treePart51_check_chunked :
    treePart51.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0,
      0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart51_check_chunked

theorem treePart51_check :
    treePart51.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0,
      0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart51_check_chunked

private theorem treePart52_check_chunked :
    treePart52.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart52_check_chunked

theorem treePart52_check :
    treePart52.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart52_check_chunked

private theorem treePart53_check_chunked :
    treePart53.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart53_check_chunked

theorem treePart53_check :
    treePart53.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart53_check_chunked

private theorem treePart54_check_chunked :
    treePart54.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart54_check_chunked

theorem treePart54_check :
    treePart54.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart54_check_chunked

private theorem treePart55_check_chunked :
    treePart55.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart55_check_chunked

theorem treePart55_check :
    treePart55.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart55_check_chunked

private theorem treePart56_check_chunked :
    treePart56.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart56_check_chunked

theorem treePart56_check :
    treePart56.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart56_check_chunked

private theorem treePart57_check_chunked :
    treePart57.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart57_check_chunked

theorem treePart57_check :
    treePart57.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart57_check_chunked

private theorem treePart58_check_chunked :
    treePart58.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart58_check_chunked

theorem treePart58_check :
    treePart58.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart58_check_chunked

private theorem treePart59_check_chunked :
    treePart59.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks6.treePart59_check_chunked

theorem treePart59_check :
    treePart59.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart59_check_chunked

private theorem treePart60_check_chunked :
    treePart60.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart60_check_chunked

theorem treePart60_check :
    treePart60.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart60_check_chunked

private theorem treePart61_check_chunked :
    treePart61.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart61_check_chunked

theorem treePart61_check :
    treePart61.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0,
      0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart61_check_chunked

private theorem treePart62_check_chunked :
    treePart62.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart62_check_chunked

theorem treePart62_check :
    treePart62.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart62_check_chunked

private theorem treePart63_check_chunked :
    treePart63.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart63_check_chunked

theorem treePart63_check :
    treePart63.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart63_check_chunked

private theorem treePart64_check_chunked :
    treePart64.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++
      [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart64_check_chunked

theorem treePart64_check :
    treePart64.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++
      [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart64_check_chunked

private theorem treePart65_check_chunked :
    treePart65.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart65_check_chunked

theorem treePart65_check :
    treePart65.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart65_check_chunked

private theorem treePart66_check_chunked :
    treePart66.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart66_check_chunked

theorem treePart66_check :
    treePart66.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart66_check_chunked

private theorem treePart67_check_chunked :
    treePart67.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart67_check_chunked

theorem treePart67_check :
    treePart67.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart67_check_chunked

private theorem treePart68_check_chunked :
    treePart68.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0,
      0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart68_check_chunked

theorem treePart68_check :
    treePart68.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0,
      0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart68_check_chunked

private theorem treePart69_check_chunked :
    treePart69.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart69_check_chunked

theorem treePart69_check :
    treePart69.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart69_check_chunked

private theorem treePart70_check_chunked :
    treePart70.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart70_check_chunked

theorem treePart70_check :
    treePart70.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart70_check_chunked

private theorem treePart71_check_chunked :
    treePart71.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart71_check_chunked

theorem treePart71_check :
    treePart71.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart71_check_chunked

private theorem treePart72_check_chunked :
    treePart72.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart72_check_chunked

theorem treePart72_check :
    treePart72.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart72_check_chunked

private theorem treePart73_check_chunked :
    treePart73.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart73_check_chunked

theorem treePart73_check :
    treePart73.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart73_check_chunked

private theorem treePart74_check_chunked :
    treePart74.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart74_check_chunked

theorem treePart74_check :
    treePart74.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart74_check_chunked

private theorem treePart75_check_chunked :
    treePart75.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart75_check_chunked

theorem treePart75_check :
    treePart75.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart75_check_chunked

private theorem treePart76_check_chunked :
    treePart76.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart76_check_chunked

theorem treePart76_check :
    treePart76.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart76_check_chunked

private theorem treePart77_check_chunked :
    treePart77.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart77_check_chunked

theorem treePart77_check :
    treePart77.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart77_check_chunked

private theorem treePart78_check_chunked :
    treePart78.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart78_check_chunked

theorem treePart78_check :
    treePart78.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart78_check_chunked

private theorem treePart79_check_chunked :
    treePart79.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])])
      = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart79_check_chunked

theorem treePart79_check :
    treePart79.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])])
      = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart79_check_chunked

private theorem treePart80_check_chunked :
    treePart80.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart80_check_chunked

theorem treePart80_check :
    treePart80.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart80_check_chunked

private theorem treePart81_check_chunked :
    treePart81.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart81_check_chunked

theorem treePart81_check :
    treePart81.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart81_check_chunked

private theorem treePart82_check_chunked :
    treePart82.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart82_check_chunked

theorem treePart82_check :
    treePart82.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart82_check_chunked

private theorem treePart83_check_chunked :
    treePart83.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks7.treePart83_check_chunked

theorem treePart83_check :
    treePart83.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart83_check_chunked

private theorem treePart84_check_chunked :
    treePart84.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart84_check_chunked

theorem treePart84_check :
    treePart84.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart84_check_chunked

private theorem treePart85_check_chunked :
    treePart85.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart85_check_chunked

theorem treePart85_check :
    treePart85.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart85_check_chunked

private theorem treePart86_check_chunked :
    treePart86.checkLookup splitForms farkasReceiptLookup cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true
      := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart86_check_chunked

theorem treePart86_check :
    treePart86.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true
      := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart86_check_chunked

private theorem treePart87_check_chunked :
    treePart87.checkLookup splitForms farkasReceiptLookup cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart87_check_chunked

theorem treePart87_check :
    treePart87.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart87_check_chunked

private theorem treePart88_check_chunked :
    treePart88.checkLookup splitForms farkasReceiptLookup cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart88_check_chunked

theorem treePart88_check :
    treePart88.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart88_check_chunked

private theorem treePart89_check_chunked :
    treePart89.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart89_check_chunked

theorem treePart89_check :
    treePart89.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart89_check_chunked

private theorem treePart90_check_chunked :
    treePart90.checkLookup splitForms farkasReceiptLookup cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1,
      0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart90_check_chunked

theorem treePart90_check :
    treePart90.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1,
      0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart90_check_chunked

private theorem treePart91_check_chunked :
    treePart91.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart91_check_chunked

theorem treePart91_check :
    treePart91.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart91_check_chunked

private theorem treePart92_check_chunked :
    treePart92.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart92_check_chunked

theorem treePart92_check :
    treePart92.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart92_check_chunked

private theorem treePart93_check_chunked :
    treePart93.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart93_check_chunked

theorem treePart93_check :
    treePart93.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart93_check_chunked

private theorem treePart94_check_chunked :
    treePart94.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++
      [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart94_check_chunked

theorem treePart94_check :
    treePart94.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++
      [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart94_check_chunked

private theorem treePart95_check_chunked :
    treePart95.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart95_check_chunked

theorem treePart95_check :
    treePart95.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart95_check_chunked

private theorem treePart96_check_chunked :
    treePart96.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1,
      0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart96_check_chunked

theorem treePart96_check :
    treePart96.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1,
      0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1,
      0, 1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart96_check_chunked

private theorem treePart97_check_chunked :
    treePart97.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true
      := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart97_check_chunked

theorem treePart97_check :
    treePart97.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true
      := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart97_check_chunked

private theorem treePart98_check_chunked :
    treePart98.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart98_check_chunked

theorem treePart98_check :
    treePart98.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart98_check_chunked

private theorem treePart99_check_chunked :
    treePart99.checkLookup splitForms farkasReceiptLookup cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart99_check_chunked

theorem treePart99_check :
    treePart99.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart99_check_chunked

private theorem treePart100_check_chunked :
    treePart100.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart100_check_chunked

theorem treePart100_check :
    treePart100.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart100_check_chunked

private theorem treePart101_check_chunked :
    treePart101.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart101_check_chunked

theorem treePart101_check :
    treePart101.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart101_check_chunked

private theorem treePart102_check_chunked :
    treePart102.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart102_check_chunked

theorem treePart102_check :
    treePart102.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
      0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart102_check_chunked

private theorem treePart103_check_chunked :
    treePart103.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks8.treePart103_check_chunked

theorem treePart103_check :
    treePart103.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart103_check_chunked

private theorem treePart104_check_chunked :
    treePart104.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
      0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart104_check_chunked

theorem treePart104_check :
    treePart104.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
      0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart104_check_chunked

private theorem treePart105_check_chunked :
    treePart105.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks8.treePart105_check_chunked

theorem treePart105_check :
    treePart105.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart105_check_chunked

private theorem treePart106_check_chunked :
    treePart106.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart106_check_chunked

theorem treePart106_check :
    treePart106.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart106_check_chunked

private theorem treePart107_check_chunked :
    treePart107.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks8.treePart107_check_chunked

theorem treePart107_check :
    treePart107.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart107_check_chunked

private theorem treePart108_check_chunked :
    treePart108.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart108_check_chunked

theorem treePart108_check :
    treePart108.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,
      -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart108_check_chunked

private theorem treePart109_check_chunked :
    treePart109.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0,
      0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart109_check_chunked

theorem treePart109_check :
    treePart109.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0,
      0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart109_check_chunked

private theorem treePart110_check_chunked :
    treePart110.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart110_check_chunked

theorem treePart110_check :
    treePart110.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart110_check_chunked

private theorem treePart111_check_chunked :
    treePart111.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0,
      0, 1, 0, 0, 0, -1, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart111_check_chunked

theorem treePart111_check :
    treePart111.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0,
      0, 1, 0, 0, 0, -1, 0, 0, 0, -1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart111_check_chunked

private theorem treePart112_check_chunked :
    treePart112.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart112_check_chunked

theorem treePart112_check :
    treePart112.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart112_check_chunked

private theorem treePart113_check_chunked :
    treePart113.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart113_check_chunked

theorem treePart113_check :
    treePart113.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0,
      0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart113_check_chunked

private theorem treePart114_check_chunked :
    treePart114.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart114_check_chunked

theorem treePart114_check :
    treePart114.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart114_check_chunked

private theorem treePart115_check_chunked :
    treePart115.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart115_check_chunked

theorem treePart115_check :
    treePart115.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) =
      true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart115_check_chunked

private theorem treePart116_check_chunked :
    treePart116.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0,
      1, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart116_check_chunked

theorem treePart116_check :
    treePart116.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0,
      1, 0, 0, 0, -1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart116_check_chunked

private theorem treePart117_check_chunked :
    treePart117.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart117_check_chunked

theorem treePart117_check :
    treePart117.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart117_check_chunked

private theorem treePart118_check_chunked :
    treePart118.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0,
      0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart118_check_chunked

theorem treePart118_check :
    treePart118.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0,
      0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart118_check_chunked

private theorem treePart119_check_chunked :
    treePart119.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0,
      1, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart119_check_chunked

theorem treePart119_check :
    treePart119.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0,
      1, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart119_check_chunked

private theorem treePart120_check_chunked :
    treePart120.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart120_check_chunked

theorem treePart120_check :
    treePart120.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart120_check_chunked

private theorem treePart121_check_chunked :
    treePart121.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart121_check_chunked

theorem treePart121_check :
    treePart121.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, -1, 1, 0, 0,
      0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart121_check_chunked

private theorem treePart122_check_chunked :
    treePart122.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart122_check_chunked

theorem treePart122_check :
    treePart122.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart122_check_chunked

private theorem treePart123_check_chunked :
    treePart123.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart123_check_chunked

theorem treePart123_check :
    treePart123.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]])
      = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart123_check_chunked

private theorem treePart124_check_chunked :
    treePart124.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart124_check_chunked

theorem treePart124_check :
    treePart124.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart124_check_chunked

private theorem treePart125_check_chunked :
    treePart125.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart125_check_chunked

theorem treePart125_check :
    treePart125.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart125_check_chunked

private theorem treePart126_check_chunked :
    treePart126.checkLookup splitForms farkasReceiptLookup cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart126_check_chunked

theorem treePart126_check :
    treePart126.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart126_check_chunked

private theorem treePart127_check_chunked :
    treePart127.checkLookup splitForms farkasReceiptLookup cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart127_check_chunked

theorem treePart127_check :
    treePart127.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart127_check_chunked

private theorem treePart128_check_chunked :
    treePart128.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0,
      0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart128_check_chunked

theorem treePart128_check :
    treePart128.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0,
      0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart128_check_chunked

private theorem treePart129_check_chunked :
    treePart129.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true :=
      by
  as_aux_lemma =>
    exact ReplayChecks9.treePart129_check_chunked

theorem treePart129_check :
    treePart129.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1,
      0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true :=
      by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart129_check_chunked

private theorem treePart130_check_chunked :
    treePart130.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart130_check_chunked

theorem treePart130_check :
    treePart130.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart130_check_chunked

private theorem treePart131_check_chunked :
    treePart131.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0,
      0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks9.treePart131_check_chunked

theorem treePart131_check :
    treePart131.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0,
      0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart131_check_chunked

private theorem treePart132_check_chunked :
    treePart132.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      0, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact ReplayChecks10.treePart132_check_chunked

theorem treePart132_check :
    treePart132.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1,
      0, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart132_check_chunked

private theorem treePart133_check_chunked :
    treePart133.checkLookup splitForms farkasReceiptLookup cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact ReplayChecks10.treePart133_check_chunked

theorem treePart133_check :
    treePart133.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1])]) = true := by
  as_aux_lemma =>
    exact (CompactCellTree.checkLookup_eq_check _ _ _ _
      farkasReceiptLookup_eq_getD _ _).symm.trans treePart133_check_chunked

theorem treeAssemblyBranch0_check :
    treeAssemblyBranch0.check splitForms farkasReceipts cells
      ((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
        0, 1, 0, 0, 0, 0]]) = true := by
  simp only [treeAssemblyBranch0, CompactCellTree.check_split, Bool.and_true, splitForm2,
    splitForm3, splitForm4, splitForm5, splitForm6, splitForm7, splitForm8, splitForm9,
    splitForm10, splitForm11, splitForm12, splitForm13, splitForm14, splitForm15, splitForm16,
    splitForm17, splitForm18, splitForm19, splitForm20, splitForm21, splitForm22,
    treePart0_check, treePart1_check, treePart10_check, treePart11_check, treePart12_check,
    treePart13_check, treePart14_check, treePart15_check, treePart16_check, treePart17_check,
    treePart18_check, treePart19_check, treePart2_check, treePart20_check, treePart21_check,
    treePart22_check, treePart23_check, treePart24_check, treePart25_check, treePart26_check,
    treePart27_check, treePart28_check, treePart29_check, treePart3_check, treePart30_check,
    treePart31_check, treePart32_check, treePart33_check, treePart34_check, treePart35_check,
    treePart36_check, treePart37_check, treePart38_check, treePart39_check, treePart4_check,
    treePart40_check, treePart41_check, treePart42_check, treePart43_check, treePart44_check,
    treePart45_check, treePart46_check, treePart47_check, treePart48_check, treePart49_check,
    treePart5_check, treePart50_check, treePart51_check, treePart52_check, treePart53_check,
    treePart54_check, treePart55_check, treePart56_check, treePart57_check, treePart58_check,
    treePart59_check, treePart6_check, treePart60_check, treePart61_check, treePart62_check,
    treePart63_check, treePart7_check, treePart8_check, treePart9_check]

theorem treeAssemblyBranch1_check :
    treeAssemblyBranch1.check splitForms farkasReceipts cells
      ((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
        [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  simp only [treeAssemblyBranch1, CompactCellTree.check_split, Bool.and_true, splitForm3,
    splitForm4, splitForm5, splitForm6, splitForm7, splitForm9, splitForm10, splitForm11,
    splitForm13, splitForm14, splitForm16, splitForm17, splitForm18, splitForm19, splitForm21,
    splitForm23, splitForm24, splitForm25, splitForm26, splitForm27, treePart100_check,
    treePart101_check, treePart64_check, treePart65_check, treePart66_check, treePart67_check,
    treePart68_check, treePart69_check, treePart70_check, treePart71_check, treePart72_check,
    treePart73_check, treePart74_check, treePart75_check, treePart76_check, treePart77_check,
    treePart78_check, treePart79_check, treePart80_check, treePart81_check, treePart82_check,
    treePart83_check, treePart84_check, treePart85_check, treePart86_check, treePart87_check,
    treePart88_check, treePart89_check, treePart90_check, treePart91_check, treePart92_check,
    treePart93_check, treePart94_check, treePart95_check, treePart96_check, treePart97_check,
    treePart98_check, treePart99_check]

theorem treeAssemblyBranch2_check :
    treeAssemblyBranch2.check splitForms farkasReceipts cells
      (base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  simp only [treeAssemblyBranch2, CompactCellTree.check_split, Bool.and_true, splitForm1,
    treeAssemblyBranch0_check, treeAssemblyBranch1_check]

theorem treeAssemblyBranch3_check :
    treeAssemblyBranch3.check splitForms farkasReceipts cells
      (base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true :=
        by
  simp only [treeAssemblyBranch3, CompactCellTree.check_split, Bool.and_true, splitForm8,
    splitForm10, splitForm15, splitForm23, splitForm26, splitForm28, splitForm29, splitForm30,
    splitForm31, splitForm32, splitForm33, splitForm34, splitForm35, splitForm36, splitForm37,
    splitForm38, splitForm39, treePart102_check, treePart103_check, treePart104_check,
    treePart105_check, treePart106_check, treePart107_check, treePart108_check,
    treePart109_check, treePart110_check, treePart111_check, treePart112_check,
    treePart113_check, treePart114_check, treePart115_check, treePart116_check,
    treePart117_check, treePart118_check, treePart119_check, treePart120_check,
    treePart121_check, treePart122_check, treePart123_check, treePart124_check,
    treePart125_check, treePart126_check, treePart127_check, treePart128_check,
    treePart129_check, treePart130_check, treePart131_check, treePart132_check,
    treePart133_check]

theorem cells_check :
    cells.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [cells, cell0_check, cell1_check, cell2_check, cell3_check, cell4_check, cell5_check,
    cell6_check, cell7_check, cell8_check, cell9_check, cell10_check, cell11_check, cell12_check,
    cell13_check, cell14_check, cell15_check, cell16_check, cell17_check, cell18_check,
    cell19_check, cell20_check, cell21_check, cell22_check, cell23_check, cell24_check,
    cell25_check, cell26_check, cell27_check, cell28_check, cell29_check, cell30_check,
    cell31_check, cell32_check, cell33_check, cell34_check, cell35_check, cell36_check,
    cell37_check, cell38_check, cell39_check, cell40_check, cell41_check, cell42_check,
    cell43_check, cell44_check, cell45_check, cell46_check, cell47_check, cell48_check,
    cell49_check, cell50_check, cell51_check, cell52_check, cell53_check, cell54_check,
    cell55_check, cell56_check, cell57_check, cell58_check, cell59_check, cell60_check,
    cell61_check, cell62_check, cell63_check, cell64_check, cell65_check, cell66_check,
    cell67_check, cell68_check, cell69_check, cell70_check, cell71_check, cell72_check,
    cell73_check, cell74_check, cell75_check, cell76_check, cell77_check, cell78_check,
    cell79_check, cell80_check, cell81_check, cell82_check, cell83_check, cell84_check,
    cell85_check, cell86_check, cell87_check, cell88_check, cell89_check, cell90_check,
    cell91_check, cell92_check, cell93_check, cell94_check, cell95_check, cell96_check,
    cell97_check, cell98_check, cell99_check, cell100_check, cell101_check, cell102_check,
    cell103_check, cell104_check, cell105_check, cell106_check, cell107_check]

theorem cells_valid : ∀ cell ∈ cells, cell.certificate.ValidClosed 4 := by
  intro cell hCell
  have hChecks := (List.all_eq_true.mp cells_check) cell hCell
  exact (ExplicitPotential.CertificateData.checkClosed_eq_true_iff _ _).mp hChecks

theorem tree_check :
    tree.check splitForms farkasReceipts cells base = true := by
  simp only [tree, CompactCellTree.check_split, Bool.and_true, splitForm0,
    treeAssemblyBranch2_check, treeAssemblyBranch3_check]

theorem base_holds (length : Fin 12 → ℕ) :
    ExplicitPotential.FormsHold base (lengthPoint length) := by
  intro form hForm
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hForm
  rcases hForm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp [aff,
    _root_.Utilities.Certificate.AffineCover.AffineForm.Holds,
    _root_.Utilities.Certificate.AffineCover.AffineForm.eval,
    lengthPoint, Fin.sum_univ_succ]

theorem closedConstruction :
    ClosedSubdivisionDharConstruction row03Core (by norm_num) :=
  closedConstruction_of_compactCellTree (by norm_num) row03_connected
    cells base splitForms farkasReceipts tree base_holds cells_valid tree_check

end AtanasovRanganathan.GenusFiveRow03FixedCover
