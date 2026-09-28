/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT563200014`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3620ccdfd7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1102 : AngleCell :=
  childHL (childLL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1103 : AngleCell :=
  childHH (childLL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `11003330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1101)))
/-- Subcell `11012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11012333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11012333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1101)))
/-- Subcell `11013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1101)))
/-- Subcell `11013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11013333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11013333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1101)))
/-- Subcell `11102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1110)))
/-- Subcell `11102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11102333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11102333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1110)))
/-- Subcell `11103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1110)))
/-- Subcell `11103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11103333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11103333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1110)))
/-- Subcell `11112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1111)))
/-- Subcell `11112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1111)))

end CertificateCells3620ccdfd7

open CertificateCells3620ccdfd7
theorem e24KC2ThetaAboveLeaf110033301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003330) = true := by
  have h : ((childLH thetaAboveCell11003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003330) h
theorem e24KC2ThetaAboveLeaf110033302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003330) = true := by
  have h : ((childHL thetaAboveCell11003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003330) h
theorem e24KC2ThetaAboveLeaf110033303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003330) = true := by
  have h : ((childHH thetaAboveCell11003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003330) h
theorem e24KC2ThetaAboveLeaf110033310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003331) = true := by
  have h : ((childLL thetaAboveCell11003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003331) h
theorem e24KC2ThetaAboveLeaf110033311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003331) = true := by
  have h : ((childLH thetaAboveCell11003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003331) h
theorem e24KC2ThetaAboveLeaf110033312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003331) = true := by
  have h : ((childHL thetaAboveCell11003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003331) h
theorem e24KC2ThetaAboveLeaf110033313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003331) = true := by
  have h : ((childHH thetaAboveCell11003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003331) h
theorem e24KC2ThetaAboveLeaf11003332 :
    adaptiveCoverCheck 11 thetaAboveCell11003332 = true := by
  have h : (thetaAboveCell11003332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003332 h
theorem e24KC2ThetaAboveLeaf11003333 :
    adaptiveCoverCheck 11 thetaAboveCell11003333 = true := by
  have h : (thetaAboveCell11003333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003333 h
theorem e24KC2ThetaAboveLeaf110100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1101)) = true := by
  have h : ((childLL (childLL thetaAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1101)) h
theorem e24KC2ThetaAboveLeaf110101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1101)) = true := by
  have h : ((childLH (childLL thetaAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1101)) h
theorem e24KC2ThetaAboveLeaf110102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1101)) = true := by
  have h : ((childHL (childLL thetaAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1101)) h
theorem e24KC2ThetaAboveLeaf110103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1101)) = true := by
  have h : ((childHH (childLL thetaAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1101)) h
theorem e24KC2ThetaAboveLeaf110110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1101)) = true := by
  have h : ((childLL (childLH thetaAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1101)) h
theorem e24KC2ThetaAboveLeaf110111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1101)) = true := by
  have h : ((childLH (childLH thetaAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1101)) h
theorem e24KC2ThetaAboveLeaf110112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1101)) = true := by
  have h : ((childHL (childLH thetaAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1101)) h
theorem e24KC2ThetaAboveLeaf110113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1101)) = true := by
  have h : ((childHH (childLH thetaAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1101)) h
theorem e24KC2ThetaAboveLeaf1101200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1101))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1101))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell1101))) = true := by
  have h : ((childHL (childLL (childHL thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell1101))) = true := by
  have h : ((childHH (childLL (childHL thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1101))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1101))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell1101))) = true := by
  have h : ((childHL (childLH (childHL thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell1101))) = true := by
  have h : ((childHH (childLH (childHL thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf11012200 :
    adaptiveCoverCheck 11 thetaAboveCell11012200 = true := by
  have h : (thetaAboveCell11012200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012200 h
theorem e24KC2ThetaAboveLeaf11012201 :
    adaptiveCoverCheck 11 thetaAboveCell11012201 = true := by
  have h : (thetaAboveCell11012201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012201 h
theorem e24KC2ThetaAboveLeaf110122020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012202) = true := by
  have h : ((childLL thetaAboveCell11012202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012202) h
theorem e24KC2ThetaAboveLeaf110122021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012202) = true := by
  have h : ((childLH thetaAboveCell11012202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012202) h
theorem e24KC2ThetaAboveLeaf110122022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012202) = true := by
  have h : ((childHL thetaAboveCell11012202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012202) h
theorem e24KC2ThetaAboveLeaf110122023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012202) = true := by
  have h : ((childHH thetaAboveCell11012202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012202) h
theorem e24KC2ThetaAboveLeaf110122030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012203) = true := by
  have h : ((childLL thetaAboveCell11012203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012203) h
theorem e24KC2ThetaAboveLeaf110122031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012203) = true := by
  have h : ((childLH thetaAboveCell11012203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012203) h
theorem e24KC2ThetaAboveLeaf110122032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012203) = true := by
  have h : ((childHL thetaAboveCell11012203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012203) h
theorem e24KC2ThetaAboveLeaf110122033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012203) = true := by
  have h : ((childHH thetaAboveCell11012203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012203) h
theorem e24KC2ThetaAboveLeaf11012210 :
    adaptiveCoverCheck 11 thetaAboveCell11012210 = true := by
  have h : (thetaAboveCell11012210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012210 h
theorem e24KC2ThetaAboveLeaf11012211 :
    adaptiveCoverCheck 11 thetaAboveCell11012211 = true := by
  have h : (thetaAboveCell11012211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012211 h
theorem e24KC2ThetaAboveLeaf110122120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012212) = true := by
  have h : ((childLL thetaAboveCell11012212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012212) h
theorem e24KC2ThetaAboveLeaf110122121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012212) = true := by
  have h : ((childLH thetaAboveCell11012212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012212) h
theorem e24KC2ThetaAboveLeaf110122122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012212) = true := by
  have h : ((childHL thetaAboveCell11012212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012212) h
theorem e24KC2ThetaAboveLeaf110122123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012212) = true := by
  have h : ((childHH thetaAboveCell11012212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012212) h
theorem e24KC2ThetaAboveLeaf110122130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012213) = true := by
  have h : ((childLL thetaAboveCell11012213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012213) h
theorem e24KC2ThetaAboveLeaf110122131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012213) = true := by
  have h : ((childLH thetaAboveCell11012213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012213) h
theorem e24KC2ThetaAboveLeaf110122132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012213) = true := by
  have h : ((childHL thetaAboveCell11012213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012213) h
theorem e24KC2ThetaAboveLeaf110122133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012213) = true := by
  have h : ((childHH thetaAboveCell11012213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012213) h
theorem e24KC2ThetaAboveLeaf110122200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012220) = true := by
  have h : ((childLL thetaAboveCell11012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012220) h
theorem e24KC2ThetaAboveLeaf110122201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012220) = true := by
  have h : ((childLH thetaAboveCell11012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012220) h
theorem e24KC2ThetaAboveLeaf110122202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012220) = true := by
  have h : ((childHL thetaAboveCell11012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012220) h
theorem e24KC2ThetaAboveLeaf110122203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012220) = true := by
  have h : ((childHH thetaAboveCell11012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012220) h
theorem e24KC2ThetaAboveLeaf110122210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012221) = true := by
  have h : ((childLL thetaAboveCell11012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012221) h
theorem e24KC2ThetaAboveLeaf110122211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012221) = true := by
  have h : ((childLH thetaAboveCell11012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012221) h
theorem e24KC2ThetaAboveLeaf110122212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012221) = true := by
  have h : ((childHL thetaAboveCell11012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012221) h
theorem e24KC2ThetaAboveLeaf110122213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012221) = true := by
  have h : ((childHH thetaAboveCell11012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012221) h
theorem e24KC2ThetaAboveLeaf11012222 :
    adaptiveCoverCheck 11 thetaAboveCell11012222 = true := by
  have h : (thetaAboveCell11012222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012222 h
theorem e24KC2ThetaAboveLeaf11012223 :
    adaptiveCoverCheck 11 thetaAboveCell11012223 = true := by
  have h : (thetaAboveCell11012223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012223 h
theorem e24KC2ThetaAboveLeaf110122300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012230) = true := by
  have h : ((childLL thetaAboveCell11012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012230) h
theorem e24KC2ThetaAboveLeaf110122301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012230) = true := by
  have h : ((childLH thetaAboveCell11012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012230) h
theorem e24KC2ThetaAboveLeaf110122302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012230) = true := by
  have h : ((childHL thetaAboveCell11012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012230) h
theorem e24KC2ThetaAboveLeaf110122303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012230) = true := by
  have h : ((childHH thetaAboveCell11012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012230) h
theorem e24KC2ThetaAboveLeaf110122310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012231) = true := by
  have h : ((childLL thetaAboveCell11012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012231) h
theorem e24KC2ThetaAboveLeaf110122311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012231) = true := by
  have h : ((childLH thetaAboveCell11012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012231) h
theorem e24KC2ThetaAboveLeaf110122312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012231) = true := by
  have h : ((childHL thetaAboveCell11012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012231) h
theorem e24KC2ThetaAboveLeaf110122313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012231) = true := by
  have h : ((childHH thetaAboveCell11012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012231) h
theorem e24KC2ThetaAboveLeaf11012232 :
    adaptiveCoverCheck 11 thetaAboveCell11012232 = true := by
  have h : (thetaAboveCell11012232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012232 h
theorem e24KC2ThetaAboveLeaf11012233 :
    adaptiveCoverCheck 11 thetaAboveCell11012233 = true := by
  have h : (thetaAboveCell11012233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012233 h
theorem e24KC2ThetaAboveLeaf11012300 :
    adaptiveCoverCheck 11 thetaAboveCell11012300 = true := by
  have h : (thetaAboveCell11012300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012300 h
theorem e24KC2ThetaAboveLeaf11012301 :
    adaptiveCoverCheck 11 thetaAboveCell11012301 = true := by
  have h : (thetaAboveCell11012301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012301 h
theorem e24KC2ThetaAboveLeaf110123020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012302) = true := by
  have h : ((childLL thetaAboveCell11012302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012302) h
theorem e24KC2ThetaAboveLeaf110123021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012302) = true := by
  have h : ((childLH thetaAboveCell11012302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012302) h
theorem e24KC2ThetaAboveLeaf110123022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012302) = true := by
  have h : ((childHL thetaAboveCell11012302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012302) h
theorem e24KC2ThetaAboveLeaf110123023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012302) = true := by
  have h : ((childHH thetaAboveCell11012302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012302) h
theorem e24KC2ThetaAboveLeaf110123030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012303) = true := by
  have h : ((childLL thetaAboveCell11012303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012303) h
theorem e24KC2ThetaAboveLeaf110123031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012303) = true := by
  have h : ((childLH thetaAboveCell11012303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012303) h
theorem e24KC2ThetaAboveLeaf110123032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012303) = true := by
  have h : ((childHL thetaAboveCell11012303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012303) h
theorem e24KC2ThetaAboveLeaf110123033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012303) = true := by
  have h : ((childHH thetaAboveCell11012303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012303) h
theorem e24KC2ThetaAboveLeaf11012310 :
    adaptiveCoverCheck 11 thetaAboveCell11012310 = true := by
  have h : (thetaAboveCell11012310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012310 h
theorem e24KC2ThetaAboveLeaf11012311 :
    adaptiveCoverCheck 11 thetaAboveCell11012311 = true := by
  have h : (thetaAboveCell11012311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012311 h
theorem e24KC2ThetaAboveLeaf110123120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012312) = true := by
  have h : ((childLL thetaAboveCell11012312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012312) h
theorem e24KC2ThetaAboveLeaf110123121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012312) = true := by
  have h : ((childLH thetaAboveCell11012312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012312) h
theorem e24KC2ThetaAboveLeaf110123122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012312) = true := by
  have h : ((childHL thetaAboveCell11012312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012312) h
theorem e24KC2ThetaAboveLeaf110123123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012312) = true := by
  have h : ((childHH thetaAboveCell11012312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012312) h
theorem e24KC2ThetaAboveLeaf110123130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012313) = true := by
  have h : ((childLL thetaAboveCell11012313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012313) h
theorem e24KC2ThetaAboveLeaf110123131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012313) = true := by
  have h : ((childLH thetaAboveCell11012313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012313) h
theorem e24KC2ThetaAboveLeaf110123132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012313) = true := by
  have h : ((childHL thetaAboveCell11012313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012313) h
theorem e24KC2ThetaAboveLeaf110123133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012313) = true := by
  have h : ((childHH thetaAboveCell11012313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012313) h
theorem e24KC2ThetaAboveLeaf110123200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012320) = true := by
  have h : ((childLL thetaAboveCell11012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012320) h
theorem e24KC2ThetaAboveLeaf110123201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012320) = true := by
  have h : ((childLH thetaAboveCell11012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012320) h
theorem e24KC2ThetaAboveLeaf110123202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012320) = true := by
  have h : ((childHL thetaAboveCell11012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012320) h
theorem e24KC2ThetaAboveLeaf110123203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012320) = true := by
  have h : ((childHH thetaAboveCell11012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012320) h
theorem e24KC2ThetaAboveLeaf110123210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012321) = true := by
  have h : ((childLL thetaAboveCell11012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012321) h
theorem e24KC2ThetaAboveLeaf110123211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012321) = true := by
  have h : ((childLH thetaAboveCell11012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012321) h
theorem e24KC2ThetaAboveLeaf110123212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012321) = true := by
  have h : ((childHL thetaAboveCell11012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012321) h
theorem e24KC2ThetaAboveLeaf110123213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012321) = true := by
  have h : ((childHH thetaAboveCell11012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012321) h
theorem e24KC2ThetaAboveLeaf11012322 :
    adaptiveCoverCheck 11 thetaAboveCell11012322 = true := by
  have h : (thetaAboveCell11012322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012322 h
theorem e24KC2ThetaAboveLeaf11012323 :
    adaptiveCoverCheck 11 thetaAboveCell11012323 = true := by
  have h : (thetaAboveCell11012323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012323 h
theorem e24KC2ThetaAboveLeaf110123300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012330) = true := by
  have h : ((childLL thetaAboveCell11012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012330) h
theorem e24KC2ThetaAboveLeaf110123301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012330) = true := by
  have h : ((childLH thetaAboveCell11012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012330) h
theorem e24KC2ThetaAboveLeaf110123302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012330) = true := by
  have h : ((childHL thetaAboveCell11012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012330) h
theorem e24KC2ThetaAboveLeaf110123303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012330) = true := by
  have h : ((childHH thetaAboveCell11012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012330) h
theorem e24KC2ThetaAboveLeaf110123310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11012331) = true := by
  have h : ((childLL thetaAboveCell11012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11012331) h
theorem e24KC2ThetaAboveLeaf110123311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11012331) = true := by
  have h : ((childLH thetaAboveCell11012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11012331) h
theorem e24KC2ThetaAboveLeaf110123312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11012331) = true := by
  have h : ((childHL thetaAboveCell11012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11012331) h
theorem e24KC2ThetaAboveLeaf110123313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11012331) = true := by
  have h : ((childHH thetaAboveCell11012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11012331) h
theorem e24KC2ThetaAboveLeaf11012332 :
    adaptiveCoverCheck 11 thetaAboveCell11012332 = true := by
  have h : (thetaAboveCell11012332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012332 h
theorem e24KC2ThetaAboveLeaf11012333 :
    adaptiveCoverCheck 11 thetaAboveCell11012333 = true := by
  have h : (thetaAboveCell11012333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11012333 h
theorem e24KC2ThetaAboveLeaf1101300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1101))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1101))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1101))) = true := by
  have h : ((childHL (childLL (childHH thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1101))) = true := by
  have h : ((childHH (childLL (childHH thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1101))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1101))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1101))) = true := by
  have h : ((childHL (childLH (childHH thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf1101313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1101))) = true := by
  have h : ((childHH (childLH (childHH thetaAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH thetaAboveCell1101))) h
theorem e24KC2ThetaAboveLeaf11013200 :
    adaptiveCoverCheck 11 thetaAboveCell11013200 = true := by
  have h : (thetaAboveCell11013200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013200 h
theorem e24KC2ThetaAboveLeaf11013201 :
    adaptiveCoverCheck 11 thetaAboveCell11013201 = true := by
  have h : (thetaAboveCell11013201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013201 h
theorem e24KC2ThetaAboveLeaf110132020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013202) = true := by
  have h : ((childLL thetaAboveCell11013202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013202) h
theorem e24KC2ThetaAboveLeaf110132021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013202) = true := by
  have h : ((childLH thetaAboveCell11013202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013202) h
theorem e24KC2ThetaAboveLeaf110132022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013202) = true := by
  have h : ((childHL thetaAboveCell11013202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013202) h
theorem e24KC2ThetaAboveLeaf110132023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013202) = true := by
  have h : ((childHH thetaAboveCell11013202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013202) h
theorem e24KC2ThetaAboveLeaf110132030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013203) = true := by
  have h : ((childLL thetaAboveCell11013203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013203) h
theorem e24KC2ThetaAboveLeaf110132031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013203) = true := by
  have h : ((childLH thetaAboveCell11013203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013203) h
theorem e24KC2ThetaAboveLeaf110132032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013203) = true := by
  have h : ((childHL thetaAboveCell11013203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013203) h
theorem e24KC2ThetaAboveLeaf110132033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013203) = true := by
  have h : ((childHH thetaAboveCell11013203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013203) h
theorem e24KC2ThetaAboveLeaf11013210 :
    adaptiveCoverCheck 11 thetaAboveCell11013210 = true := by
  have h : (thetaAboveCell11013210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013210 h
theorem e24KC2ThetaAboveLeaf11013211 :
    adaptiveCoverCheck 11 thetaAboveCell11013211 = true := by
  have h : (thetaAboveCell11013211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013211 h
theorem e24KC2ThetaAboveLeaf110132120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013212) = true := by
  have h : ((childLL thetaAboveCell11013212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013212) h
theorem e24KC2ThetaAboveLeaf110132121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013212) = true := by
  have h : ((childLH thetaAboveCell11013212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013212) h
theorem e24KC2ThetaAboveLeaf110132122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013212) = true := by
  have h : ((childHL thetaAboveCell11013212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013212) h
theorem e24KC2ThetaAboveLeaf110132123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013212) = true := by
  have h : ((childHH thetaAboveCell11013212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013212) h
theorem e24KC2ThetaAboveLeaf110132130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013213) = true := by
  have h : ((childLL thetaAboveCell11013213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013213) h
theorem e24KC2ThetaAboveLeaf110132131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013213) = true := by
  have h : ((childLH thetaAboveCell11013213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013213) h
theorem e24KC2ThetaAboveLeaf110132132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013213) = true := by
  have h : ((childHL thetaAboveCell11013213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013213) h
theorem e24KC2ThetaAboveLeaf110132133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013213) = true := by
  have h : ((childHH thetaAboveCell11013213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013213) h
theorem e24KC2ThetaAboveLeaf110132200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013220) = true := by
  have h : ((childLL thetaAboveCell11013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013220) h
theorem e24KC2ThetaAboveLeaf110132201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013220) = true := by
  have h : ((childLH thetaAboveCell11013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013220) h
theorem e24KC2ThetaAboveLeaf110132202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013220) = true := by
  have h : ((childHL thetaAboveCell11013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013220) h
theorem e24KC2ThetaAboveLeaf110132203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013220) = true := by
  have h : ((childHH thetaAboveCell11013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013220) h
theorem e24KC2ThetaAboveLeaf110132210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013221) = true := by
  have h : ((childLL thetaAboveCell11013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013221) h
theorem e24KC2ThetaAboveLeaf110132211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013221) = true := by
  have h : ((childLH thetaAboveCell11013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013221) h
theorem e24KC2ThetaAboveLeaf110132212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013221) = true := by
  have h : ((childHL thetaAboveCell11013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013221) h
theorem e24KC2ThetaAboveLeaf110132213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013221) = true := by
  have h : ((childHH thetaAboveCell11013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013221) h
theorem e24KC2ThetaAboveLeaf11013222 :
    adaptiveCoverCheck 11 thetaAboveCell11013222 = true := by
  have h : (thetaAboveCell11013222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013222 h
theorem e24KC2ThetaAboveLeaf11013223 :
    adaptiveCoverCheck 11 thetaAboveCell11013223 = true := by
  have h : (thetaAboveCell11013223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013223 h
theorem e24KC2ThetaAboveLeaf110132300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013230) = true := by
  have h : ((childLL thetaAboveCell11013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013230) h
theorem e24KC2ThetaAboveLeaf110132301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013230) = true := by
  have h : ((childLH thetaAboveCell11013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013230) h
theorem e24KC2ThetaAboveLeaf110132302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013230) = true := by
  have h : ((childHL thetaAboveCell11013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013230) h
theorem e24KC2ThetaAboveLeaf110132303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013230) = true := by
  have h : ((childHH thetaAboveCell11013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013230) h
theorem e24KC2ThetaAboveLeaf110132310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013231) = true := by
  have h : ((childLL thetaAboveCell11013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013231) h
theorem e24KC2ThetaAboveLeaf110132311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013231) = true := by
  have h : ((childLH thetaAboveCell11013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013231) h
theorem e24KC2ThetaAboveLeaf110132312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013231) = true := by
  have h : ((childHL thetaAboveCell11013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013231) h
theorem e24KC2ThetaAboveLeaf110132313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013231) = true := by
  have h : ((childHH thetaAboveCell11013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013231) h
theorem e24KC2ThetaAboveLeaf11013232 :
    adaptiveCoverCheck 11 thetaAboveCell11013232 = true := by
  have h : (thetaAboveCell11013232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013232 h
theorem e24KC2ThetaAboveLeaf11013233 :
    adaptiveCoverCheck 11 thetaAboveCell11013233 = true := by
  have h : (thetaAboveCell11013233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013233 h
theorem e24KC2ThetaAboveLeaf11013300 :
    adaptiveCoverCheck 11 thetaAboveCell11013300 = true := by
  have h : (thetaAboveCell11013300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013300 h
theorem e24KC2ThetaAboveLeaf11013301 :
    adaptiveCoverCheck 11 thetaAboveCell11013301 = true := by
  have h : (thetaAboveCell11013301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013301 h
theorem e24KC2ThetaAboveLeaf110133020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013302) = true := by
  have h : ((childLL thetaAboveCell11013302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013302) h
theorem e24KC2ThetaAboveLeaf110133021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013302) = true := by
  have h : ((childLH thetaAboveCell11013302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013302) h
theorem e24KC2ThetaAboveLeaf110133022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013302) = true := by
  have h : ((childHL thetaAboveCell11013302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013302) h
theorem e24KC2ThetaAboveLeaf110133023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013302) = true := by
  have h : ((childHH thetaAboveCell11013302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013302) h
theorem e24KC2ThetaAboveLeaf110133030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013303) = true := by
  have h : ((childLL thetaAboveCell11013303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013303) h
theorem e24KC2ThetaAboveLeaf110133031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013303) = true := by
  have h : ((childLH thetaAboveCell11013303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013303) h
theorem e24KC2ThetaAboveLeaf110133032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013303) = true := by
  have h : ((childHL thetaAboveCell11013303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013303) h
theorem e24KC2ThetaAboveLeaf110133033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013303) = true := by
  have h : ((childHH thetaAboveCell11013303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013303) h
theorem e24KC2ThetaAboveLeaf11013310 :
    adaptiveCoverCheck 11 thetaAboveCell11013310 = true := by
  have h : (thetaAboveCell11013310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013310 h
theorem e24KC2ThetaAboveLeaf11013311 :
    adaptiveCoverCheck 11 thetaAboveCell11013311 = true := by
  have h : (thetaAboveCell11013311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013311 h
theorem e24KC2ThetaAboveLeaf110133120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013312) = true := by
  have h : ((childLL thetaAboveCell11013312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013312) h
theorem e24KC2ThetaAboveLeaf110133121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013312) = true := by
  have h : ((childLH thetaAboveCell11013312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013312) h
theorem e24KC2ThetaAboveLeaf110133122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013312) = true := by
  have h : ((childHL thetaAboveCell11013312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013312) h
theorem e24KC2ThetaAboveLeaf110133123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013312) = true := by
  have h : ((childHH thetaAboveCell11013312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013312) h
theorem e24KC2ThetaAboveLeaf110133130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013313) = true := by
  have h : ((childLL thetaAboveCell11013313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013313) h
theorem e24KC2ThetaAboveLeaf110133131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013313) = true := by
  have h : ((childLH thetaAboveCell11013313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013313) h
theorem e24KC2ThetaAboveLeaf110133132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013313) = true := by
  have h : ((childHL thetaAboveCell11013313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013313) h
theorem e24KC2ThetaAboveLeaf110133133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013313) = true := by
  have h : ((childHH thetaAboveCell11013313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013313) h
theorem e24KC2ThetaAboveLeaf110133200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013320) = true := by
  have h : ((childLL thetaAboveCell11013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013320) h
theorem e24KC2ThetaAboveLeaf110133201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013320) = true := by
  have h : ((childLH thetaAboveCell11013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013320) h
theorem e24KC2ThetaAboveLeaf110133202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013320) = true := by
  have h : ((childHL thetaAboveCell11013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013320) h
theorem e24KC2ThetaAboveLeaf110133203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013320) = true := by
  have h : ((childHH thetaAboveCell11013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013320) h
theorem e24KC2ThetaAboveLeaf110133210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013321) = true := by
  have h : ((childLL thetaAboveCell11013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013321) h
theorem e24KC2ThetaAboveLeaf110133211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013321) = true := by
  have h : ((childLH thetaAboveCell11013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013321) h
theorem e24KC2ThetaAboveLeaf110133212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013321) = true := by
  have h : ((childHL thetaAboveCell11013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013321) h
theorem e24KC2ThetaAboveLeaf110133213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013321) = true := by
  have h : ((childHH thetaAboveCell11013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013321) h
theorem e24KC2ThetaAboveLeaf11013322 :
    adaptiveCoverCheck 11 thetaAboveCell11013322 = true := by
  have h : (thetaAboveCell11013322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013322 h
theorem e24KC2ThetaAboveLeaf11013323 :
    adaptiveCoverCheck 11 thetaAboveCell11013323 = true := by
  have h : (thetaAboveCell11013323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013323 h
theorem e24KC2ThetaAboveLeaf110133300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013330) = true := by
  have h : ((childLL thetaAboveCell11013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013330) h
theorem e24KC2ThetaAboveLeaf110133301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013330) = true := by
  have h : ((childLH thetaAboveCell11013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013330) h
theorem e24KC2ThetaAboveLeaf110133302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013330) = true := by
  have h : ((childHL thetaAboveCell11013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013330) h
theorem e24KC2ThetaAboveLeaf110133303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013330) = true := by
  have h : ((childHH thetaAboveCell11013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013330) h
theorem e24KC2ThetaAboveLeaf110133310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11013331) = true := by
  have h : ((childLL thetaAboveCell11013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11013331) h
theorem e24KC2ThetaAboveLeaf110133311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11013331) = true := by
  have h : ((childLH thetaAboveCell11013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11013331) h
theorem e24KC2ThetaAboveLeaf110133312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11013331) = true := by
  have h : ((childHL thetaAboveCell11013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11013331) h
theorem e24KC2ThetaAboveLeaf110133313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11013331) = true := by
  have h : ((childHH thetaAboveCell11013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11013331) h
theorem e24KC2ThetaAboveLeaf11013332 :
    adaptiveCoverCheck 11 thetaAboveCell11013332 = true := by
  have h : (thetaAboveCell11013332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013332 h
theorem e24KC2ThetaAboveLeaf11013333 :
    adaptiveCoverCheck 11 thetaAboveCell11013333 = true := by
  have h : (thetaAboveCell11013333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11013333 h
theorem e24KC2ThetaAboveLeaf1102000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1102))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1102))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1102))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1102))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1102))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1102))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1102))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1102))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf110202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1102)) = true := by
  have h : ((childHL (childLL thetaAboveCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1102)) h
theorem e24KC2ThetaAboveLeaf110203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1102)) = true := by
  have h : ((childHH (childLL thetaAboveCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1102)) h
theorem e24KC2ThetaAboveLeaf1102100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1102))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1102))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1102))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1102))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1102))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1102))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1102))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf1102113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1102))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1102))) h
theorem e24KC2ThetaAboveLeaf110212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1102)) = true := by
  have h : ((childHL (childLH thetaAboveCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1102)) h
theorem e24KC2ThetaAboveLeaf110213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1102)) = true := by
  have h : ((childHH (childLH thetaAboveCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1102)) h
theorem e24KC2ThetaAboveLeaf11022 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1102) = true := by
  have h : ((childHL thetaAboveCell1102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1102) h
theorem e24KC2ThetaAboveLeaf11023 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1102) = true := by
  have h : ((childHH thetaAboveCell1102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1102) h
theorem e24KC2ThetaAboveLeaf1103000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1103))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1103))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1103))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1103))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1103))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1103))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1103))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1103))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf110302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1103)) = true := by
  have h : ((childHL (childLL thetaAboveCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1103)) h
theorem e24KC2ThetaAboveLeaf110303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1103)) = true := by
  have h : ((childHH (childLL thetaAboveCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1103)) h
theorem e24KC2ThetaAboveLeaf1103100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1103))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1103))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1103))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1103))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1103))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1103))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1103))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf1103113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1103))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1103))) h
theorem e24KC2ThetaAboveLeaf110312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1103)) = true := by
  have h : ((childHL (childLH thetaAboveCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1103)) h
theorem e24KC2ThetaAboveLeaf110313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1103)) = true := by
  have h : ((childHH (childLH thetaAboveCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1103)) h
theorem e24KC2ThetaAboveLeaf11032 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1103) = true := by
  have h : ((childHL thetaAboveCell1103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1103) h
theorem e24KC2ThetaAboveLeaf11033 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1103) = true := by
  have h : ((childHH thetaAboveCell1103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1103) h
theorem e24KC2ThetaAboveLeaf111000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1110)) = true := by
  have h : ((childLL (childLL thetaAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1110)) h
theorem e24KC2ThetaAboveLeaf111001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1110)) = true := by
  have h : ((childLH (childLL thetaAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1110)) h
theorem e24KC2ThetaAboveLeaf111002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1110)) = true := by
  have h : ((childHL (childLL thetaAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1110)) h
theorem e24KC2ThetaAboveLeaf111003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1110)) = true := by
  have h : ((childHH (childLL thetaAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1110)) h
theorem e24KC2ThetaAboveLeaf111010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1110)) = true := by
  have h : ((childLL (childLH thetaAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1110)) h
theorem e24KC2ThetaAboveLeaf111011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1110)) = true := by
  have h : ((childLH (childLH thetaAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1110)) h
theorem e24KC2ThetaAboveLeaf111012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1110)) = true := by
  have h : ((childHL (childLH thetaAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1110)) h
theorem e24KC2ThetaAboveLeaf111013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1110)) = true := by
  have h : ((childHH (childLH thetaAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1110)) h
theorem e24KC2ThetaAboveLeaf1110200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1110))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1110))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell1110))) = true := by
  have h : ((childHL (childLL (childHL thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell1110))) = true := by
  have h : ((childHH (childLL (childHL thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1110))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1110))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell1110))) = true := by
  have h : ((childHL (childLH (childHL thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell1110))) = true := by
  have h : ((childHH (childLH (childHL thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf11102200 :
    adaptiveCoverCheck 11 thetaAboveCell11102200 = true := by
  have h : (thetaAboveCell11102200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102200 h
theorem e24KC2ThetaAboveLeaf11102201 :
    adaptiveCoverCheck 11 thetaAboveCell11102201 = true := by
  have h : (thetaAboveCell11102201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102201 h
theorem e24KC2ThetaAboveLeaf111022020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102202) = true := by
  have h : ((childLL thetaAboveCell11102202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102202) h
theorem e24KC2ThetaAboveLeaf111022021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102202) = true := by
  have h : ((childLH thetaAboveCell11102202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102202) h
theorem e24KC2ThetaAboveLeaf111022022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102202) = true := by
  have h : ((childHL thetaAboveCell11102202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102202) h
theorem e24KC2ThetaAboveLeaf111022023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102202) = true := by
  have h : ((childHH thetaAboveCell11102202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102202) h
theorem e24KC2ThetaAboveLeaf111022030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102203) = true := by
  have h : ((childLL thetaAboveCell11102203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102203) h
theorem e24KC2ThetaAboveLeaf111022031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102203) = true := by
  have h : ((childLH thetaAboveCell11102203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102203) h
theorem e24KC2ThetaAboveLeaf111022032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102203) = true := by
  have h : ((childHL thetaAboveCell11102203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102203) h
theorem e24KC2ThetaAboveLeaf111022033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102203) = true := by
  have h : ((childHH thetaAboveCell11102203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102203) h
theorem e24KC2ThetaAboveLeaf11102210 :
    adaptiveCoverCheck 11 thetaAboveCell11102210 = true := by
  have h : (thetaAboveCell11102210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102210 h
theorem e24KC2ThetaAboveLeaf11102211 :
    adaptiveCoverCheck 11 thetaAboveCell11102211 = true := by
  have h : (thetaAboveCell11102211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102211 h
theorem e24KC2ThetaAboveLeaf111022120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102212) = true := by
  have h : ((childLL thetaAboveCell11102212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102212) h
theorem e24KC2ThetaAboveLeaf111022121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102212) = true := by
  have h : ((childLH thetaAboveCell11102212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102212) h
theorem e24KC2ThetaAboveLeaf111022122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102212) = true := by
  have h : ((childHL thetaAboveCell11102212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102212) h
theorem e24KC2ThetaAboveLeaf111022123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102212) = true := by
  have h : ((childHH thetaAboveCell11102212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102212) h
theorem e24KC2ThetaAboveLeaf111022130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102213) = true := by
  have h : ((childLL thetaAboveCell11102213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102213) h
theorem e24KC2ThetaAboveLeaf111022131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102213) = true := by
  have h : ((childLH thetaAboveCell11102213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102213) h
theorem e24KC2ThetaAboveLeaf111022132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102213) = true := by
  have h : ((childHL thetaAboveCell11102213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102213) h
theorem e24KC2ThetaAboveLeaf111022133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102213) = true := by
  have h : ((childHH thetaAboveCell11102213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102213) h
theorem e24KC2ThetaAboveLeaf111022200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102220) = true := by
  have h : ((childLL thetaAboveCell11102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102220) h
theorem e24KC2ThetaAboveLeaf111022201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102220) = true := by
  have h : ((childLH thetaAboveCell11102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102220) h
theorem e24KC2ThetaAboveLeaf111022202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102220) = true := by
  have h : ((childHL thetaAboveCell11102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102220) h
theorem e24KC2ThetaAboveLeaf111022203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102220) = true := by
  have h : ((childHH thetaAboveCell11102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102220) h
theorem e24KC2ThetaAboveLeaf111022210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102221) = true := by
  have h : ((childLL thetaAboveCell11102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102221) h
theorem e24KC2ThetaAboveLeaf111022211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102221) = true := by
  have h : ((childLH thetaAboveCell11102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102221) h
theorem e24KC2ThetaAboveLeaf111022212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102221) = true := by
  have h : ((childHL thetaAboveCell11102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102221) h
theorem e24KC2ThetaAboveLeaf111022213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102221) = true := by
  have h : ((childHH thetaAboveCell11102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102221) h
theorem e24KC2ThetaAboveLeaf11102222 :
    adaptiveCoverCheck 11 thetaAboveCell11102222 = true := by
  have h : (thetaAboveCell11102222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102222 h
theorem e24KC2ThetaAboveLeaf11102223 :
    adaptiveCoverCheck 11 thetaAboveCell11102223 = true := by
  have h : (thetaAboveCell11102223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102223 h
theorem e24KC2ThetaAboveLeaf111022300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102230) = true := by
  have h : ((childLL thetaAboveCell11102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102230) h
theorem e24KC2ThetaAboveLeaf111022301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102230) = true := by
  have h : ((childLH thetaAboveCell11102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102230) h
theorem e24KC2ThetaAboveLeaf111022302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102230) = true := by
  have h : ((childHL thetaAboveCell11102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102230) h
theorem e24KC2ThetaAboveLeaf111022303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102230) = true := by
  have h : ((childHH thetaAboveCell11102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102230) h
theorem e24KC2ThetaAboveLeaf111022310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102231) = true := by
  have h : ((childLL thetaAboveCell11102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102231) h
theorem e24KC2ThetaAboveLeaf111022311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102231) = true := by
  have h : ((childLH thetaAboveCell11102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102231) h
theorem e24KC2ThetaAboveLeaf111022312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102231) = true := by
  have h : ((childHL thetaAboveCell11102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102231) h
theorem e24KC2ThetaAboveLeaf111022313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102231) = true := by
  have h : ((childHH thetaAboveCell11102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102231) h
theorem e24KC2ThetaAboveLeaf11102232 :
    adaptiveCoverCheck 11 thetaAboveCell11102232 = true := by
  have h : (thetaAboveCell11102232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102232 h
theorem e24KC2ThetaAboveLeaf11102233 :
    adaptiveCoverCheck 11 thetaAboveCell11102233 = true := by
  have h : (thetaAboveCell11102233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102233 h
theorem e24KC2ThetaAboveLeaf11102300 :
    adaptiveCoverCheck 11 thetaAboveCell11102300 = true := by
  have h : (thetaAboveCell11102300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102300 h
theorem e24KC2ThetaAboveLeaf11102301 :
    adaptiveCoverCheck 11 thetaAboveCell11102301 = true := by
  have h : (thetaAboveCell11102301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102301 h
theorem e24KC2ThetaAboveLeaf111023020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102302) = true := by
  have h : ((childLL thetaAboveCell11102302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102302) h
theorem e24KC2ThetaAboveLeaf111023021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102302) = true := by
  have h : ((childLH thetaAboveCell11102302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102302) h
theorem e24KC2ThetaAboveLeaf111023022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102302) = true := by
  have h : ((childHL thetaAboveCell11102302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102302) h
theorem e24KC2ThetaAboveLeaf111023023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102302) = true := by
  have h : ((childHH thetaAboveCell11102302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102302) h
theorem e24KC2ThetaAboveLeaf111023030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102303) = true := by
  have h : ((childLL thetaAboveCell11102303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102303) h
theorem e24KC2ThetaAboveLeaf111023031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102303) = true := by
  have h : ((childLH thetaAboveCell11102303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102303) h
theorem e24KC2ThetaAboveLeaf111023032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102303) = true := by
  have h : ((childHL thetaAboveCell11102303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102303) h
theorem e24KC2ThetaAboveLeaf111023033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102303) = true := by
  have h : ((childHH thetaAboveCell11102303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102303) h
theorem e24KC2ThetaAboveLeaf11102310 :
    adaptiveCoverCheck 11 thetaAboveCell11102310 = true := by
  have h : (thetaAboveCell11102310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102310 h
theorem e24KC2ThetaAboveLeaf11102311 :
    adaptiveCoverCheck 11 thetaAboveCell11102311 = true := by
  have h : (thetaAboveCell11102311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102311 h
theorem e24KC2ThetaAboveLeaf111023120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102312) = true := by
  have h : ((childLL thetaAboveCell11102312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102312) h
theorem e24KC2ThetaAboveLeaf111023121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102312) = true := by
  have h : ((childLH thetaAboveCell11102312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102312) h
theorem e24KC2ThetaAboveLeaf111023122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102312) = true := by
  have h : ((childHL thetaAboveCell11102312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102312) h
theorem e24KC2ThetaAboveLeaf111023123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102312) = true := by
  have h : ((childHH thetaAboveCell11102312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102312) h
theorem e24KC2ThetaAboveLeaf111023130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102313) = true := by
  have h : ((childLL thetaAboveCell11102313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102313) h
theorem e24KC2ThetaAboveLeaf111023131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102313) = true := by
  have h : ((childLH thetaAboveCell11102313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102313) h
theorem e24KC2ThetaAboveLeaf111023132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102313) = true := by
  have h : ((childHL thetaAboveCell11102313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102313) h
theorem e24KC2ThetaAboveLeaf111023133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102313) = true := by
  have h : ((childHH thetaAboveCell11102313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102313) h
theorem e24KC2ThetaAboveLeaf111023200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102320) = true := by
  have h : ((childLL thetaAboveCell11102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102320) h
theorem e24KC2ThetaAboveLeaf111023201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102320) = true := by
  have h : ((childLH thetaAboveCell11102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102320) h
theorem e24KC2ThetaAboveLeaf111023202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102320) = true := by
  have h : ((childHL thetaAboveCell11102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102320) h
theorem e24KC2ThetaAboveLeaf111023203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102320) = true := by
  have h : ((childHH thetaAboveCell11102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102320) h
theorem e24KC2ThetaAboveLeaf111023210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102321) = true := by
  have h : ((childLL thetaAboveCell11102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102321) h
theorem e24KC2ThetaAboveLeaf111023211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102321) = true := by
  have h : ((childLH thetaAboveCell11102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102321) h
theorem e24KC2ThetaAboveLeaf111023212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102321) = true := by
  have h : ((childHL thetaAboveCell11102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102321) h
theorem e24KC2ThetaAboveLeaf111023213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102321) = true := by
  have h : ((childHH thetaAboveCell11102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102321) h
theorem e24KC2ThetaAboveLeaf11102322 :
    adaptiveCoverCheck 11 thetaAboveCell11102322 = true := by
  have h : (thetaAboveCell11102322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102322 h
theorem e24KC2ThetaAboveLeaf11102323 :
    adaptiveCoverCheck 11 thetaAboveCell11102323 = true := by
  have h : (thetaAboveCell11102323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102323 h
theorem e24KC2ThetaAboveLeaf111023300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102330) = true := by
  have h : ((childLL thetaAboveCell11102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102330) h
theorem e24KC2ThetaAboveLeaf111023301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102330) = true := by
  have h : ((childLH thetaAboveCell11102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102330) h
theorem e24KC2ThetaAboveLeaf111023302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102330) = true := by
  have h : ((childHL thetaAboveCell11102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102330) h
theorem e24KC2ThetaAboveLeaf111023303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102330) = true := by
  have h : ((childHH thetaAboveCell11102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102330) h
theorem e24KC2ThetaAboveLeaf111023310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11102331) = true := by
  have h : ((childLL thetaAboveCell11102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11102331) h
theorem e24KC2ThetaAboveLeaf111023311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11102331) = true := by
  have h : ((childLH thetaAboveCell11102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11102331) h
theorem e24KC2ThetaAboveLeaf111023312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11102331) = true := by
  have h : ((childHL thetaAboveCell11102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11102331) h
theorem e24KC2ThetaAboveLeaf111023313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11102331) = true := by
  have h : ((childHH thetaAboveCell11102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11102331) h
theorem e24KC2ThetaAboveLeaf11102332 :
    adaptiveCoverCheck 11 thetaAboveCell11102332 = true := by
  have h : (thetaAboveCell11102332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102332 h
theorem e24KC2ThetaAboveLeaf11102333 :
    adaptiveCoverCheck 11 thetaAboveCell11102333 = true := by
  have h : (thetaAboveCell11102333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11102333 h
theorem e24KC2ThetaAboveLeaf1110300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1110))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1110))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1110))) = true := by
  have h : ((childHL (childLL (childHH thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1110))) = true := by
  have h : ((childHH (childLL (childHH thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1110))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1110))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1110))) = true := by
  have h : ((childHL (childLH (childHH thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf1110313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1110))) = true := by
  have h : ((childHH (childLH (childHH thetaAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH thetaAboveCell1110))) h
theorem e24KC2ThetaAboveLeaf11103200 :
    adaptiveCoverCheck 11 thetaAboveCell11103200 = true := by
  have h : (thetaAboveCell11103200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103200 h
theorem e24KC2ThetaAboveLeaf11103201 :
    adaptiveCoverCheck 11 thetaAboveCell11103201 = true := by
  have h : (thetaAboveCell11103201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103201 h
theorem e24KC2ThetaAboveLeaf111032020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103202) = true := by
  have h : ((childLL thetaAboveCell11103202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103202) h
theorem e24KC2ThetaAboveLeaf111032021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103202) = true := by
  have h : ((childLH thetaAboveCell11103202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103202) h
theorem e24KC2ThetaAboveLeaf111032022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103202) = true := by
  have h : ((childHL thetaAboveCell11103202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103202) h
theorem e24KC2ThetaAboveLeaf111032023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103202) = true := by
  have h : ((childHH thetaAboveCell11103202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103202) h
theorem e24KC2ThetaAboveLeaf111032030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103203) = true := by
  have h : ((childLL thetaAboveCell11103203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103203) h
theorem e24KC2ThetaAboveLeaf111032031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103203) = true := by
  have h : ((childLH thetaAboveCell11103203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103203) h
theorem e24KC2ThetaAboveLeaf111032032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103203) = true := by
  have h : ((childHL thetaAboveCell11103203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103203) h
theorem e24KC2ThetaAboveLeaf111032033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103203) = true := by
  have h : ((childHH thetaAboveCell11103203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103203) h
theorem e24KC2ThetaAboveLeaf11103210 :
    adaptiveCoverCheck 11 thetaAboveCell11103210 = true := by
  have h : (thetaAboveCell11103210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103210 h
theorem e24KC2ThetaAboveLeaf11103211 :
    adaptiveCoverCheck 11 thetaAboveCell11103211 = true := by
  have h : (thetaAboveCell11103211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103211 h
theorem e24KC2ThetaAboveLeaf111032120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103212) = true := by
  have h : ((childLL thetaAboveCell11103212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103212) h
theorem e24KC2ThetaAboveLeaf111032121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103212) = true := by
  have h : ((childLH thetaAboveCell11103212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103212) h
theorem e24KC2ThetaAboveLeaf111032122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103212) = true := by
  have h : ((childHL thetaAboveCell11103212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103212) h
theorem e24KC2ThetaAboveLeaf111032123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103212) = true := by
  have h : ((childHH thetaAboveCell11103212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103212) h
theorem e24KC2ThetaAboveLeaf111032130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103213) = true := by
  have h : ((childLL thetaAboveCell11103213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103213) h
theorem e24KC2ThetaAboveLeaf111032131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103213) = true := by
  have h : ((childLH thetaAboveCell11103213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103213) h
theorem e24KC2ThetaAboveLeaf111032132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103213) = true := by
  have h : ((childHL thetaAboveCell11103213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103213) h
theorem e24KC2ThetaAboveLeaf111032133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103213) = true := by
  have h : ((childHH thetaAboveCell11103213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103213) h
theorem e24KC2ThetaAboveLeaf111032200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103220) = true := by
  have h : ((childLL thetaAboveCell11103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103220) h
theorem e24KC2ThetaAboveLeaf111032201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103220) = true := by
  have h : ((childLH thetaAboveCell11103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103220) h
theorem e24KC2ThetaAboveLeaf111032202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103220) = true := by
  have h : ((childHL thetaAboveCell11103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103220) h
theorem e24KC2ThetaAboveLeaf111032203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103220) = true := by
  have h : ((childHH thetaAboveCell11103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103220) h
theorem e24KC2ThetaAboveLeaf111032210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103221) = true := by
  have h : ((childLL thetaAboveCell11103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103221) h
theorem e24KC2ThetaAboveLeaf111032211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103221) = true := by
  have h : ((childLH thetaAboveCell11103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103221) h
theorem e24KC2ThetaAboveLeaf111032212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103221) = true := by
  have h : ((childHL thetaAboveCell11103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103221) h
theorem e24KC2ThetaAboveLeaf111032213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103221) = true := by
  have h : ((childHH thetaAboveCell11103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103221) h
theorem e24KC2ThetaAboveLeaf11103222 :
    adaptiveCoverCheck 11 thetaAboveCell11103222 = true := by
  have h : (thetaAboveCell11103222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103222 h
theorem e24KC2ThetaAboveLeaf11103223 :
    adaptiveCoverCheck 11 thetaAboveCell11103223 = true := by
  have h : (thetaAboveCell11103223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103223 h
theorem e24KC2ThetaAboveLeaf111032300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103230) = true := by
  have h : ((childLL thetaAboveCell11103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103230) h
theorem e24KC2ThetaAboveLeaf111032301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103230) = true := by
  have h : ((childLH thetaAboveCell11103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103230) h
theorem e24KC2ThetaAboveLeaf111032302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103230) = true := by
  have h : ((childHL thetaAboveCell11103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103230) h
theorem e24KC2ThetaAboveLeaf111032303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103230) = true := by
  have h : ((childHH thetaAboveCell11103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103230) h
theorem e24KC2ThetaAboveLeaf111032310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103231) = true := by
  have h : ((childLL thetaAboveCell11103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103231) h
theorem e24KC2ThetaAboveLeaf111032311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103231) = true := by
  have h : ((childLH thetaAboveCell11103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103231) h
theorem e24KC2ThetaAboveLeaf111032312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103231) = true := by
  have h : ((childHL thetaAboveCell11103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103231) h
theorem e24KC2ThetaAboveLeaf111032313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103231) = true := by
  have h : ((childHH thetaAboveCell11103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103231) h
theorem e24KC2ThetaAboveLeaf11103232 :
    adaptiveCoverCheck 11 thetaAboveCell11103232 = true := by
  have h : (thetaAboveCell11103232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103232 h
theorem e24KC2ThetaAboveLeaf11103233 :
    adaptiveCoverCheck 11 thetaAboveCell11103233 = true := by
  have h : (thetaAboveCell11103233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103233 h
theorem e24KC2ThetaAboveLeaf11103300 :
    adaptiveCoverCheck 11 thetaAboveCell11103300 = true := by
  have h : (thetaAboveCell11103300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103300 h
theorem e24KC2ThetaAboveLeaf11103301 :
    adaptiveCoverCheck 11 thetaAboveCell11103301 = true := by
  have h : (thetaAboveCell11103301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103301 h
theorem e24KC2ThetaAboveLeaf111033020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103302) = true := by
  have h : ((childLL thetaAboveCell11103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103302) h
theorem e24KC2ThetaAboveLeaf111033021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103302) = true := by
  have h : ((childLH thetaAboveCell11103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103302) h
theorem e24KC2ThetaAboveLeaf111033022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103302) = true := by
  have h : ((childHL thetaAboveCell11103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103302) h
theorem e24KC2ThetaAboveLeaf111033023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103302) = true := by
  have h : ((childHH thetaAboveCell11103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103302) h
theorem e24KC2ThetaAboveLeaf111033030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103303) = true := by
  have h : ((childLL thetaAboveCell11103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103303) h
theorem e24KC2ThetaAboveLeaf111033031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103303) = true := by
  have h : ((childLH thetaAboveCell11103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103303) h
theorem e24KC2ThetaAboveLeaf111033032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103303) = true := by
  have h : ((childHL thetaAboveCell11103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103303) h
theorem e24KC2ThetaAboveLeaf111033033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103303) = true := by
  have h : ((childHH thetaAboveCell11103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103303) h
theorem e24KC2ThetaAboveLeaf11103310 :
    adaptiveCoverCheck 11 thetaAboveCell11103310 = true := by
  have h : (thetaAboveCell11103310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103310 h
theorem e24KC2ThetaAboveLeaf11103311 :
    adaptiveCoverCheck 11 thetaAboveCell11103311 = true := by
  have h : (thetaAboveCell11103311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103311 h
theorem e24KC2ThetaAboveLeaf111033120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103312) = true := by
  have h : ((childLL thetaAboveCell11103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103312) h
theorem e24KC2ThetaAboveLeaf111033121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103312) = true := by
  have h : ((childLH thetaAboveCell11103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103312) h
theorem e24KC2ThetaAboveLeaf111033122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103312) = true := by
  have h : ((childHL thetaAboveCell11103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103312) h
theorem e24KC2ThetaAboveLeaf111033123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103312) = true := by
  have h : ((childHH thetaAboveCell11103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103312) h
theorem e24KC2ThetaAboveLeaf111033130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103313) = true := by
  have h : ((childLL thetaAboveCell11103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103313) h
theorem e24KC2ThetaAboveLeaf111033131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103313) = true := by
  have h : ((childLH thetaAboveCell11103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103313) h
theorem e24KC2ThetaAboveLeaf111033132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103313) = true := by
  have h : ((childHL thetaAboveCell11103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103313) h
theorem e24KC2ThetaAboveLeaf111033133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103313) = true := by
  have h : ((childHH thetaAboveCell11103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103313) h
theorem e24KC2ThetaAboveLeaf111033200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103320) = true := by
  have h : ((childLL thetaAboveCell11103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103320) h
theorem e24KC2ThetaAboveLeaf111033201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103320) = true := by
  have h : ((childLH thetaAboveCell11103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103320) h
theorem e24KC2ThetaAboveLeaf111033202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103320) = true := by
  have h : ((childHL thetaAboveCell11103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103320) h
theorem e24KC2ThetaAboveLeaf111033203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103320) = true := by
  have h : ((childHH thetaAboveCell11103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103320) h
theorem e24KC2ThetaAboveLeaf111033210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103321) = true := by
  have h : ((childLL thetaAboveCell11103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103321) h
theorem e24KC2ThetaAboveLeaf111033211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103321) = true := by
  have h : ((childLH thetaAboveCell11103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103321) h
theorem e24KC2ThetaAboveLeaf111033212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103321) = true := by
  have h : ((childHL thetaAboveCell11103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103321) h
theorem e24KC2ThetaAboveLeaf111033213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103321) = true := by
  have h : ((childHH thetaAboveCell11103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103321) h
theorem e24KC2ThetaAboveLeaf11103322 :
    adaptiveCoverCheck 11 thetaAboveCell11103322 = true := by
  have h : (thetaAboveCell11103322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103322 h
theorem e24KC2ThetaAboveLeaf11103323 :
    adaptiveCoverCheck 11 thetaAboveCell11103323 = true := by
  have h : (thetaAboveCell11103323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103323 h
theorem e24KC2ThetaAboveLeaf111033300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103330) = true := by
  have h : ((childLL thetaAboveCell11103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103330) h
theorem e24KC2ThetaAboveLeaf111033301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103330) = true := by
  have h : ((childLH thetaAboveCell11103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103330) h
theorem e24KC2ThetaAboveLeaf111033302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103330) = true := by
  have h : ((childHL thetaAboveCell11103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103330) h
theorem e24KC2ThetaAboveLeaf111033303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103330) = true := by
  have h : ((childHH thetaAboveCell11103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103330) h
theorem e24KC2ThetaAboveLeaf111033310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11103331) = true := by
  have h : ((childLL thetaAboveCell11103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11103331) h
theorem e24KC2ThetaAboveLeaf111033311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11103331) = true := by
  have h : ((childLH thetaAboveCell11103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11103331) h
theorem e24KC2ThetaAboveLeaf111033312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11103331) = true := by
  have h : ((childHL thetaAboveCell11103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11103331) h
theorem e24KC2ThetaAboveLeaf111033313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11103331) = true := by
  have h : ((childHH thetaAboveCell11103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11103331) h
theorem e24KC2ThetaAboveLeaf11103332 :
    adaptiveCoverCheck 11 thetaAboveCell11103332 = true := by
  have h : (thetaAboveCell11103332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103332 h
theorem e24KC2ThetaAboveLeaf11103333 :
    adaptiveCoverCheck 11 thetaAboveCell11103333 = true := by
  have h : (thetaAboveCell11103333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11103333 h
theorem e24KC2ThetaAboveLeaf111100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1111)) = true := by
  have h : ((childLL (childLL thetaAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1111)) h
theorem e24KC2ThetaAboveLeaf111101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1111)) = true := by
  have h : ((childLH (childLL thetaAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1111)) h
theorem e24KC2ThetaAboveLeaf111102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1111)) = true := by
  have h : ((childHL (childLL thetaAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1111)) h
theorem e24KC2ThetaAboveLeaf111103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1111)) = true := by
  have h : ((childHH (childLL thetaAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1111)) h
theorem e24KC2ThetaAboveLeaf111110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1111)) = true := by
  have h : ((childLL (childLH thetaAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1111)) h
theorem e24KC2ThetaAboveLeaf111111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1111)) = true := by
  have h : ((childLH (childLH thetaAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1111)) h
theorem e24KC2ThetaAboveLeaf111112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1111)) = true := by
  have h : ((childHL (childLH thetaAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1111)) h
theorem e24KC2ThetaAboveLeaf111113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1111)) = true := by
  have h : ((childHH (childLH thetaAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1111)) h
theorem e24KC2ThetaAboveLeaf1111200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1111))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1111))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell1111))) = true := by
  have h : ((childHL (childLL (childHL thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell1111))) = true := by
  have h : ((childHH (childLL (childHL thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1111))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1111))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell1111))) = true := by
  have h : ((childHL (childLH (childHL thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell1111))) = true := by
  have h : ((childHH (childLH (childHL thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf11112200 :
    adaptiveCoverCheck 11 thetaAboveCell11112200 = true := by
  have h : (thetaAboveCell11112200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112200 h
theorem e24KC2ThetaAboveLeaf11112201 :
    adaptiveCoverCheck 11 thetaAboveCell11112201 = true := by
  have h : (thetaAboveCell11112201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112201 h
theorem e24KC2ThetaAboveLeaf111122020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112202) = true := by
  have h : ((childLL thetaAboveCell11112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112202) h
theorem e24KC2ThetaAboveLeaf111122021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112202) = true := by
  have h : ((childLH thetaAboveCell11112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112202) h
theorem e24KC2ThetaAboveLeaf111122022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112202) = true := by
  have h : ((childHL thetaAboveCell11112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112202) h
theorem e24KC2ThetaAboveLeaf111122023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112202) = true := by
  have h : ((childHH thetaAboveCell11112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112202) h
theorem e24KC2ThetaAboveLeaf111122030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112203) = true := by
  have h : ((childLL thetaAboveCell11112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112203) h
theorem e24KC2ThetaAboveLeaf111122031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112203) = true := by
  have h : ((childLH thetaAboveCell11112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112203) h
theorem e24KC2ThetaAboveLeaf111122032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112203) = true := by
  have h : ((childHL thetaAboveCell11112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112203) h
theorem e24KC2ThetaAboveLeaf111122033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112203) = true := by
  have h : ((childHH thetaAboveCell11112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112203) h
theorem e24KC2ThetaAboveLeaf11112210 :
    adaptiveCoverCheck 11 thetaAboveCell11112210 = true := by
  have h : (thetaAboveCell11112210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112210 h
theorem e24KC2ThetaAboveLeaf11112211 :
    adaptiveCoverCheck 11 thetaAboveCell11112211 = true := by
  have h : (thetaAboveCell11112211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112211 h
theorem e24KC2ThetaAboveLeaf111122120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112212) = true := by
  have h : ((childLL thetaAboveCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112212) h
theorem e24KC2ThetaAboveLeaf111122121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112212) = true := by
  have h : ((childLH thetaAboveCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112212) h
theorem e24KC2ThetaAboveLeaf111122122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112212) = true := by
  have h : ((childHL thetaAboveCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112212) h
theorem e24KC2ThetaAboveLeaf111122123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112212) = true := by
  have h : ((childHH thetaAboveCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112212) h
theorem e24KC2ThetaAboveLeaf111122130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112213) = true := by
  have h : ((childLL thetaAboveCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112213) h
theorem e24KC2ThetaAboveLeaf111122131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112213) = true := by
  have h : ((childLH thetaAboveCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112213) h
theorem e24KC2ThetaAboveLeaf111122132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112213) = true := by
  have h : ((childHL thetaAboveCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112213) h
theorem e24KC2ThetaAboveLeaf111122133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112213) = true := by
  have h : ((childHH thetaAboveCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112213) h
theorem e24KC2ThetaAboveLeaf111122200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112220) = true := by
  have h : ((childLL thetaAboveCell11112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112220) h
theorem e24KC2ThetaAboveLeaf111122201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112220) = true := by
  have h : ((childLH thetaAboveCell11112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112220) h
theorem e24KC2ThetaAboveLeaf111122202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112220) = true := by
  have h : ((childHL thetaAboveCell11112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112220) h
theorem e24KC2ThetaAboveLeaf111122203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112220) = true := by
  have h : ((childHH thetaAboveCell11112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112220) h
theorem e24KC2ThetaAboveLeaf111122210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112221) = true := by
  have h : ((childLL thetaAboveCell11112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112221) h
theorem e24KC2ThetaAboveLeaf111122211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112221) = true := by
  have h : ((childLH thetaAboveCell11112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112221) h
theorem e24KC2ThetaAboveLeaf111122212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112221) = true := by
  have h : ((childHL thetaAboveCell11112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112221) h
theorem e24KC2ThetaAboveLeaf111122213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112221) = true := by
  have h : ((childHH thetaAboveCell11112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112221) h
theorem e24KC2ThetaAboveLeaf11112222 :
    adaptiveCoverCheck 11 thetaAboveCell11112222 = true := by
  have h : (thetaAboveCell11112222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112222 h
theorem e24KC2ThetaAboveLeaf11112223 :
    adaptiveCoverCheck 11 thetaAboveCell11112223 = true := by
  have h : (thetaAboveCell11112223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112223 h
theorem e24KC2ThetaAboveLeaf111122300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112230) = true := by
  have h : ((childLL thetaAboveCell11112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112230) h
theorem e24KC2ThetaAboveLeaf111122301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112230) = true := by
  have h : ((childLH thetaAboveCell11112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112230) h
theorem e24KC2ThetaAboveLeaf111122302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112230) = true := by
  have h : ((childHL thetaAboveCell11112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112230) h
theorem e24KC2ThetaAboveLeaf111122303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112230) = true := by
  have h : ((childHH thetaAboveCell11112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112230) h
theorem e24KC2ThetaAboveLeaf111122310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112231) = true := by
  have h : ((childLL thetaAboveCell11112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112231) h
theorem e24KC2ThetaAboveLeaf111122311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112231) = true := by
  have h : ((childLH thetaAboveCell11112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112231) h
theorem e24KC2ThetaAboveLeaf111122312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112231) = true := by
  have h : ((childHL thetaAboveCell11112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112231) h
theorem e24KC2ThetaAboveLeaf111122313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112231) = true := by
  have h : ((childHH thetaAboveCell11112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112231) h
theorem e24KC2ThetaAboveLeaf11112232 :
    adaptiveCoverCheck 11 thetaAboveCell11112232 = true := by
  have h : (thetaAboveCell11112232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112232 h
theorem e24KC2ThetaAboveLeaf11112233 :
    adaptiveCoverCheck 11 thetaAboveCell11112233 = true := by
  have h : (thetaAboveCell11112233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112233 h
theorem e24KC2ThetaAboveLeaf11112300 :
    adaptiveCoverCheck 11 thetaAboveCell11112300 = true := by
  have h : (thetaAboveCell11112300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112300 h
theorem e24KC2ThetaAboveLeaf11112301 :
    adaptiveCoverCheck 11 thetaAboveCell11112301 = true := by
  have h : (thetaAboveCell11112301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112301 h
theorem e24KC2ThetaAboveLeaf111123020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112302) = true := by
  have h : ((childLL thetaAboveCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112302) h
theorem e24KC2ThetaAboveLeaf111123021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112302) = true := by
  have h : ((childLH thetaAboveCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112302) h
theorem e24KC2ThetaAboveLeaf111123022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112302) = true := by
  have h : ((childHL thetaAboveCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112302) h
theorem e24KC2ThetaAboveLeaf111123023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112302) = true := by
  have h : ((childHH thetaAboveCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112302) h
theorem e24KC2ThetaAboveLeaf111123030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112303) = true := by
  have h : ((childLL thetaAboveCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112303) h
theorem e24KC2ThetaAboveLeaf111123031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112303) = true := by
  have h : ((childLH thetaAboveCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112303) h
theorem e24KC2ThetaAboveLeaf111123032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112303) = true := by
  have h : ((childHL thetaAboveCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112303) h
theorem e24KC2ThetaAboveLeaf111123033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112303) = true := by
  have h : ((childHH thetaAboveCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112303) h
theorem e24KC2ThetaAboveLeaf11112310 :
    adaptiveCoverCheck 11 thetaAboveCell11112310 = true := by
  have h : (thetaAboveCell11112310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112310 h
theorem e24KC2ThetaAboveLeaf11112311 :
    adaptiveCoverCheck 11 thetaAboveCell11112311 = true := by
  have h : (thetaAboveCell11112311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112311 h
theorem e24KC2ThetaAboveLeaf111123120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112312) = true := by
  have h : ((childLL thetaAboveCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112312) h
theorem e24KC2ThetaAboveLeaf111123121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112312) = true := by
  have h : ((childLH thetaAboveCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112312) h
theorem e24KC2ThetaAboveLeaf111123122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112312) = true := by
  have h : ((childHL thetaAboveCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112312) h
theorem e24KC2ThetaAboveLeaf111123123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112312) = true := by
  have h : ((childHH thetaAboveCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112312) h
theorem e24KC2ThetaAboveLeaf111123130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112313) = true := by
  have h : ((childLL thetaAboveCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112313) h
theorem e24KC2ThetaAboveLeaf111123131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112313) = true := by
  have h : ((childLH thetaAboveCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112313) h
theorem e24KC2ThetaAboveLeaf111123132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112313) = true := by
  have h : ((childHL thetaAboveCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112313) h
theorem e24KC2ThetaAboveLeaf111123133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112313) = true := by
  have h : ((childHH thetaAboveCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112313) h
theorem e24KC2ThetaAboveLeaf111123200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112320) = true := by
  have h : ((childLL thetaAboveCell11112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112320) h
theorem e24KC2ThetaAboveLeaf111123201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112320) = true := by
  have h : ((childLH thetaAboveCell11112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112320) h
theorem e24KC2ThetaAboveLeaf111123202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112320) = true := by
  have h : ((childHL thetaAboveCell11112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112320) h
theorem e24KC2ThetaAboveLeaf111123203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112320) = true := by
  have h : ((childHH thetaAboveCell11112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112320) h
theorem e24KC2ThetaAboveLeaf111123210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112321) = true := by
  have h : ((childLL thetaAboveCell11112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112321) h
theorem e24KC2ThetaAboveLeaf111123211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112321) = true := by
  have h : ((childLH thetaAboveCell11112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112321) h
theorem e24KC2ThetaAboveLeaf111123212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112321) = true := by
  have h : ((childHL thetaAboveCell11112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112321) h
theorem e24KC2ThetaAboveLeaf111123213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112321) = true := by
  have h : ((childHH thetaAboveCell11112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112321) h
theorem e24KC2ThetaAboveLeaf11112322 :
    adaptiveCoverCheck 11 thetaAboveCell11112322 = true := by
  have h : (thetaAboveCell11112322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112322 h
theorem e24KC2ThetaAboveLeaf11112323 :
    adaptiveCoverCheck 11 thetaAboveCell11112323 = true := by
  have h : (thetaAboveCell11112323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11112323 h
theorem e24KC2ThetaAboveLeaf111123300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112330) = true := by
  have h : ((childLL thetaAboveCell11112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112330) h
theorem e24KC2ThetaAboveLeaf111123301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112330) = true := by
  have h : ((childLH thetaAboveCell11112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112330) h
theorem e24KC2ThetaAboveLeaf111123302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112330) = true := by
  have h : ((childHL thetaAboveCell11112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112330) h
theorem e24KC2ThetaAboveLeaf111123303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112330) = true := by
  have h : ((childHH thetaAboveCell11112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112330) h
theorem e24KC2ThetaAboveLeaf111123310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112331) = true := by
  have h : ((childLL thetaAboveCell11112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112331) h

end PartE
end GerverSofa

end

end

end
