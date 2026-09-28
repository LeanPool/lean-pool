/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT204800007`.
* `KernelOnly.PartE.E24KC5TerminalBatchT256000008`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2cfecae988

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `01003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0101)))
/-- Subcell `01012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0101)))
/-- Subcell `01012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0101)))
/-- Subcell `01012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0101)))
/-- Subcell `01012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0101)))
/-- Subcell `01012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0101)))
/-- Subcell `01012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0101)))
/-- Subcell `01012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0101)))
/-- Subcell `01012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0101)))
/-- Subcell `01012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0101)))
/-- Subcell `01012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0101)))
/-- Subcell `01012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0101)))
/-- Subcell `01012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0101)))
/-- Subcell `01012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0101)))
/-- Subcell `01012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0101)))
/-- Subcell `01012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0101)))
/-- Subcell `01012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0101)))
/-- Subcell `01012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01012333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01012333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0101)))
/-- Subcell `01013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0101)))
/-- Subcell `01013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0101)))
/-- Subcell `01013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0101)))
/-- Subcell `01013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0101)))
/-- Subcell `01013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0101)))
/-- Subcell `01013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0101)))
/-- Subcell `01013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0101)))
/-- Subcell `01013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0101)))
/-- Subcell `01013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0101)))
/-- Subcell `01013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0101)))
/-- Subcell `01013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0101)))
/-- Subcell `01013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0101)))
/-- Subcell `01013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0101)))
/-- Subcell `01013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0101)))
/-- Subcell `01013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0101)))
/-- Subcell `01013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0101)))
/-- Subcell `01013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0101)))
/-- Subcell `01013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0101)))

end CertificateCells2cfecae988

open CertificateCells2cfecae988
theorem e24KC2ThetaAboveLeaf0100330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01003303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01003303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01003303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01003303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01003303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01003303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01003303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01003303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf0100330333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003303)) h
theorem e24KC2ThetaAboveLeaf010033100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003310) = true := by
  have h : ((childLL thetaAboveCell01003310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003310) h
theorem e24KC2ThetaAboveLeaf010033101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003310) = true := by
  have h : ((childLH thetaAboveCell01003310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003310) h
theorem e24KC2ThetaAboveLeaf0100331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003310)) h
theorem e24KC2ThetaAboveLeaf0100331021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003310)) h
theorem e24KC2ThetaAboveLeaf0100331022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003310)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003310)) h
theorem e24KC2ThetaAboveLeaf0100331023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003310)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003310)) h
theorem e24KC2ThetaAboveLeaf0100331030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003310)) h
theorem e24KC2ThetaAboveLeaf0100331031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003310)) h
theorem e24KC2ThetaAboveLeaf0100331032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003310)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003310)) h
theorem e24KC2ThetaAboveLeaf0100331033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003310)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003310)) h
theorem e24KC2ThetaAboveLeaf010033110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003311) = true := by
  have h : ((childLL thetaAboveCell01003311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003311) h
theorem e24KC2ThetaAboveLeaf010033111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003311) = true := by
  have h : ((childLH thetaAboveCell01003311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003311) h
theorem e24KC2ThetaAboveLeaf0100331120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003311)) h
theorem e24KC2ThetaAboveLeaf0100331121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003311)) h
theorem e24KC2ThetaAboveLeaf0100331122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003311)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003311)) h
theorem e24KC2ThetaAboveLeaf0100331123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003311)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003311)) h
theorem e24KC2ThetaAboveLeaf0100331130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003311)) h
theorem e24KC2ThetaAboveLeaf0100331131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003311)) h
theorem e24KC2ThetaAboveLeaf0100331132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003311)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003311)) h
theorem e24KC2ThetaAboveLeaf0100331133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003311)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003311)) h
theorem e24KC2ThetaAboveLeaf0100331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01003312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01003312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01003312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01003312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01003312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01003312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01003312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01003312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003312)) h
theorem e24KC2ThetaAboveLeaf0100331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01003313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01003313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01003313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01003313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01003313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01003313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01003313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01003313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf0100331333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003313)) h
theorem e24KC2ThetaAboveLeaf01003320 :
    adaptiveCoverCheck 11 thetaAboveCell01003320 = true := by
  have h : (thetaAboveCell01003320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003320 h
theorem e24KC2ThetaAboveLeaf01003321 :
    adaptiveCoverCheck 11 thetaAboveCell01003321 = true := by
  have h : (thetaAboveCell01003321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003321 h
theorem e24KC2ThetaAboveLeaf01003322 :
    adaptiveCoverCheck 11 thetaAboveCell01003322 = true := by
  have h : (thetaAboveCell01003322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003322 h
theorem e24KC2ThetaAboveLeaf01003323 :
    adaptiveCoverCheck 11 thetaAboveCell01003323 = true := by
  have h : (thetaAboveCell01003323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003323 h
theorem e24KC2ThetaAboveLeaf010033300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003330) = true := by
  have h : ((childLL thetaAboveCell01003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003330) h
theorem e24KC2ThetaAboveLeaf010033301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003330) = true := by
  have h : ((childLH thetaAboveCell01003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003330) h
theorem e24KC2ThetaAboveLeaf010033302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01003330) = true := by
  have h : ((childHL thetaAboveCell01003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01003330) h
theorem e24KC2ThetaAboveLeaf010033303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01003330) = true := by
  have h : ((childHH thetaAboveCell01003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01003330) h
theorem e24KC2ThetaAboveLeaf010033310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003331) = true := by
  have h : ((childLL thetaAboveCell01003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003331) h
theorem e24KC2ThetaAboveLeaf010033311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003331) = true := by
  have h : ((childLH thetaAboveCell01003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003331) h
theorem e24KC2ThetaAboveLeaf010033312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01003331) = true := by
  have h : ((childHL thetaAboveCell01003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01003331) h
theorem e24KC2ThetaAboveLeaf010033313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01003331) = true := by
  have h : ((childHH thetaAboveCell01003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01003331) h
theorem e24KC2ThetaAboveLeaf01003332 :
    adaptiveCoverCheck 11 thetaAboveCell01003332 = true := by
  have h : (thetaAboveCell01003332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003332 h
theorem e24KC2ThetaAboveLeaf01003333 :
    adaptiveCoverCheck 11 thetaAboveCell01003333 = true := by
  have h : (thetaAboveCell01003333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003333 h
theorem e24KC2ThetaAboveLeaf010100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0101)) = true := by
  have h : ((childLL (childLL thetaAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0101)) h
theorem e24KC2ThetaAboveLeaf010101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0101)) = true := by
  have h : ((childLH (childLL thetaAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0101)) h
theorem e24KC2ThetaAboveLeaf010102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0101)) = true := by
  have h : ((childHL (childLL thetaAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0101)) h
theorem e24KC2ThetaAboveLeaf010103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0101)) = true := by
  have h : ((childHH (childLL thetaAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0101)) h
theorem e24KC2ThetaAboveLeaf010110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0101)) = true := by
  have h : ((childLL (childLH thetaAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0101)) h
theorem e24KC2ThetaAboveLeaf010111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0101)) = true := by
  have h : ((childLH (childLH thetaAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0101)) h
theorem e24KC2ThetaAboveLeaf010112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0101)) = true := by
  have h : ((childHL (childLH thetaAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0101)) h
theorem e24KC2ThetaAboveLeaf010113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0101)) = true := by
  have h : ((childHH (childLH thetaAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0101)) h
theorem e24KC2ThetaAboveLeaf0101200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0101))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0101))) h
theorem e24KC2ThetaAboveLeaf0101201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0101))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0101))) h
theorem e24KC2ThetaAboveLeaf01012020 :
    adaptiveCoverCheck 11 thetaAboveCell01012020 = true := by
  have h : (thetaAboveCell01012020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012020 h
theorem e24KC2ThetaAboveLeaf01012021 :
    adaptiveCoverCheck 11 thetaAboveCell01012021 = true := by
  have h : (thetaAboveCell01012021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012021 h
theorem e24KC2ThetaAboveLeaf01012022 :
    adaptiveCoverCheck 11 thetaAboveCell01012022 = true := by
  have h : (thetaAboveCell01012022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012022 h
theorem e24KC2ThetaAboveLeaf01012023 :
    adaptiveCoverCheck 11 thetaAboveCell01012023 = true := by
  have h : (thetaAboveCell01012023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012023 h
theorem e24KC2ThetaAboveLeaf01012030 :
    adaptiveCoverCheck 11 thetaAboveCell01012030 = true := by
  have h : (thetaAboveCell01012030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012030 h
theorem e24KC2ThetaAboveLeaf01012031 :
    adaptiveCoverCheck 11 thetaAboveCell01012031 = true := by
  have h : (thetaAboveCell01012031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012031 h
theorem e24KC2ThetaAboveLeaf01012032 :
    adaptiveCoverCheck 11 thetaAboveCell01012032 = true := by
  have h : (thetaAboveCell01012032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012032 h
theorem e24KC2ThetaAboveLeaf01012033 :
    adaptiveCoverCheck 11 thetaAboveCell01012033 = true := by
  have h : (thetaAboveCell01012033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012033 h
theorem e24KC2ThetaAboveLeaf0101210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0101))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0101))) h
theorem e24KC2ThetaAboveLeaf0101211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0101))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0101))) h
theorem e24KC2ThetaAboveLeaf01012120 :
    adaptiveCoverCheck 11 thetaAboveCell01012120 = true := by
  have h : (thetaAboveCell01012120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012120 h
theorem e24KC2ThetaAboveLeaf01012121 :
    adaptiveCoverCheck 11 thetaAboveCell01012121 = true := by
  have h : (thetaAboveCell01012121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012121 h
theorem e24KC2ThetaAboveLeaf01012122 :
    adaptiveCoverCheck 11 thetaAboveCell01012122 = true := by
  have h : (thetaAboveCell01012122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012122 h
theorem e24KC2ThetaAboveLeaf01012123 :
    adaptiveCoverCheck 11 thetaAboveCell01012123 = true := by
  have h : (thetaAboveCell01012123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012123 h
theorem e24KC2ThetaAboveLeaf01012130 :
    adaptiveCoverCheck 11 thetaAboveCell01012130 = true := by
  have h : (thetaAboveCell01012130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012130 h
theorem e24KC2ThetaAboveLeaf01012131 :
    adaptiveCoverCheck 11 thetaAboveCell01012131 = true := by
  have h : (thetaAboveCell01012131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012131 h
theorem e24KC2ThetaAboveLeaf01012132 :
    adaptiveCoverCheck 11 thetaAboveCell01012132 = true := by
  have h : (thetaAboveCell01012132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012132 h
theorem e24KC2ThetaAboveLeaf01012133 :
    adaptiveCoverCheck 11 thetaAboveCell01012133 = true := by
  have h : (thetaAboveCell01012133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012133 h
theorem e24KC2ThetaAboveLeaf010122000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012200) = true := by
  have h : ((childLL thetaAboveCell01012200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012200) h
theorem e24KC2ThetaAboveLeaf010122001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012200) = true := by
  have h : ((childLH thetaAboveCell01012200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012200) h
theorem e24KC2ThetaAboveLeaf0101220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012200)) h
theorem e24KC2ThetaAboveLeaf0101220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012200)) h
theorem e24KC2ThetaAboveLeaf0101220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012200)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012200)) h
theorem e24KC2ThetaAboveLeaf0101220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012200)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012200)) h
theorem e24KC2ThetaAboveLeaf0101220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012200)) h
theorem e24KC2ThetaAboveLeaf0101220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012200)) h
theorem e24KC2ThetaAboveLeaf0101220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012200)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012200)) h
theorem e24KC2ThetaAboveLeaf0101220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012200)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012200)) h
theorem e24KC2ThetaAboveLeaf010122010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012201) = true := by
  have h : ((childLL thetaAboveCell01012201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012201) h
theorem e24KC2ThetaAboveLeaf010122011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012201) = true := by
  have h : ((childLH thetaAboveCell01012201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012201) h
theorem e24KC2ThetaAboveLeaf0101220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012201)) h
theorem e24KC2ThetaAboveLeaf0101220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012201)) h
theorem e24KC2ThetaAboveLeaf0101220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012201)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012201)) h
theorem e24KC2ThetaAboveLeaf0101220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012201)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012201)) h
theorem e24KC2ThetaAboveLeaf0101220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012201)) h
theorem e24KC2ThetaAboveLeaf0101220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012201)) h
theorem e24KC2ThetaAboveLeaf0101220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012201)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012201)) h
theorem e24KC2ThetaAboveLeaf0101220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012201)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012201)) h
theorem e24KC2ThetaAboveLeaf0101220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01012202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01012202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01012202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01012202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01012202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01012202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01012202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01012202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012202)) h
theorem e24KC2ThetaAboveLeaf0101220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01012203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01012203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01012203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01012203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01012203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01012203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01012203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01012203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf0101220333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012203)) h
theorem e24KC2ThetaAboveLeaf010122100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012210) = true := by
  have h : ((childLL thetaAboveCell01012210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012210) h
theorem e24KC2ThetaAboveLeaf010122101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012210) = true := by
  have h : ((childLH thetaAboveCell01012210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012210) h
theorem e24KC2ThetaAboveLeaf0101221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012210)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012210)) h
theorem e24KC2ThetaAboveLeaf0101221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012210)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012210)) h
theorem e24KC2ThetaAboveLeaf0101221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012210)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012210)) h
theorem e24KC2ThetaAboveLeaf0101221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012210)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012210)) h
theorem e24KC2ThetaAboveLeaf0101221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012210)) h
theorem e24KC2ThetaAboveLeaf0101221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012210)) h
theorem e24KC2ThetaAboveLeaf0101221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012210)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012210)) h
theorem e24KC2ThetaAboveLeaf0101221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012210)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012210)) h
theorem e24KC2ThetaAboveLeaf010122110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012211) = true := by
  have h : ((childLL thetaAboveCell01012211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012211) h
theorem e24KC2ThetaAboveLeaf010122111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012211) = true := by
  have h : ((childLH thetaAboveCell01012211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012211) h
theorem e24KC2ThetaAboveLeaf0101221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012211)) h
theorem e24KC2ThetaAboveLeaf0101221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012211)) h
theorem e24KC2ThetaAboveLeaf0101221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012211)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012211)) h
theorem e24KC2ThetaAboveLeaf0101221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012211)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012211)) h
theorem e24KC2ThetaAboveLeaf0101221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012211)) h
theorem e24KC2ThetaAboveLeaf0101221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012211)) h
theorem e24KC2ThetaAboveLeaf0101221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012211)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012211)) h
theorem e24KC2ThetaAboveLeaf0101221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012211)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012211)) h
theorem e24KC2ThetaAboveLeaf0101221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01012212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01012212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01012212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01012212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01012212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01012212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01012212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01012212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012212)) h
theorem e24KC2ThetaAboveLeaf0101221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01012213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01012213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01012213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01012213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01012213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01012213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01012213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01012213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf0101221333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012213)) h
theorem e24KC2ThetaAboveLeaf010122200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012220) = true := by
  have h : ((childLL thetaAboveCell01012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012220) h
theorem e24KC2ThetaAboveLeaf010122201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012220) = true := by
  have h : ((childLH thetaAboveCell01012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012220) h
theorem e24KC2ThetaAboveLeaf010122202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01012220) = true := by
  have h : ((childHL thetaAboveCell01012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01012220) h
theorem e24KC2ThetaAboveLeaf010122203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01012220) = true := by
  have h : ((childHH thetaAboveCell01012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01012220) h
theorem e24KC2ThetaAboveLeaf010122210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012221) = true := by
  have h : ((childLL thetaAboveCell01012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012221) h
theorem e24KC2ThetaAboveLeaf010122211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012221) = true := by
  have h : ((childLH thetaAboveCell01012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012221) h
theorem e24KC2ThetaAboveLeaf010122212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01012221) = true := by
  have h : ((childHL thetaAboveCell01012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01012221) h
theorem e24KC2ThetaAboveLeaf010122213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01012221) = true := by
  have h : ((childHH thetaAboveCell01012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01012221) h
theorem e24KC2ThetaAboveLeaf01012222 :
    adaptiveCoverCheck 11 thetaAboveCell01012222 = true := by
  have h : (thetaAboveCell01012222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012222 h
theorem e24KC2ThetaAboveLeaf01012223 :
    adaptiveCoverCheck 11 thetaAboveCell01012223 = true := by
  have h : (thetaAboveCell01012223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012223 h
theorem e24KC2ThetaAboveLeaf010122300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012230) = true := by
  have h : ((childLL thetaAboveCell01012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012230) h
theorem e24KC2ThetaAboveLeaf010122301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012230) = true := by
  have h : ((childLH thetaAboveCell01012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012230) h
theorem e24KC2ThetaAboveLeaf010122302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01012230) = true := by
  have h : ((childHL thetaAboveCell01012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01012230) h
theorem e24KC2ThetaAboveLeaf010122303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01012230) = true := by
  have h : ((childHH thetaAboveCell01012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01012230) h
theorem e24KC2ThetaAboveLeaf010122310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012231) = true := by
  have h : ((childLL thetaAboveCell01012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012231) h
theorem e24KC2ThetaAboveLeaf010122311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012231) = true := by
  have h : ((childLH thetaAboveCell01012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012231) h
theorem e24KC2ThetaAboveLeaf010122312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01012231) = true := by
  have h : ((childHL thetaAboveCell01012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01012231) h
theorem e24KC2ThetaAboveLeaf010122313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01012231) = true := by
  have h : ((childHH thetaAboveCell01012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01012231) h
theorem e24KC2ThetaAboveLeaf01012232 :
    adaptiveCoverCheck 11 thetaAboveCell01012232 = true := by
  have h : (thetaAboveCell01012232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012232 h
theorem e24KC2ThetaAboveLeaf01012233 :
    adaptiveCoverCheck 11 thetaAboveCell01012233 = true := by
  have h : (thetaAboveCell01012233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012233 h
theorem e24KC2ThetaAboveLeaf010123000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012300) = true := by
  have h : ((childLL thetaAboveCell01012300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012300) h
theorem e24KC2ThetaAboveLeaf010123001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012300) = true := by
  have h : ((childLH thetaAboveCell01012300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012300) h
theorem e24KC2ThetaAboveLeaf0101230020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012300)) h
theorem e24KC2ThetaAboveLeaf0101230021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012300)) h
theorem e24KC2ThetaAboveLeaf0101230022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012300)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012300)) h
theorem e24KC2ThetaAboveLeaf0101230023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012300)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012300)) h
theorem e24KC2ThetaAboveLeaf0101230030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012300)) h
theorem e24KC2ThetaAboveLeaf0101230031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012300)) h
theorem e24KC2ThetaAboveLeaf0101230032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012300)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012300)) h
theorem e24KC2ThetaAboveLeaf0101230033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012300)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012300)) h
theorem e24KC2ThetaAboveLeaf010123010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012301) = true := by
  have h : ((childLL thetaAboveCell01012301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012301) h
theorem e24KC2ThetaAboveLeaf010123011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012301) = true := by
  have h : ((childLH thetaAboveCell01012301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012301) h
theorem e24KC2ThetaAboveLeaf0101230120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012301)) h
theorem e24KC2ThetaAboveLeaf0101230121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012301)) h
theorem e24KC2ThetaAboveLeaf0101230122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012301)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012301)) h
theorem e24KC2ThetaAboveLeaf0101230123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012301)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012301)) h
theorem e24KC2ThetaAboveLeaf0101230130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012301)) h
theorem e24KC2ThetaAboveLeaf0101230131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012301)) h
theorem e24KC2ThetaAboveLeaf0101230132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012301)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012301)) h
theorem e24KC2ThetaAboveLeaf0101230133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012301)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012301)) h
theorem e24KC2ThetaAboveLeaf0101230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01012302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01012302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01012302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01012302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01012302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01012302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01012302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01012302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012302)) h
theorem e24KC2ThetaAboveLeaf0101230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01012303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01012303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01012303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01012303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01012303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01012303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01012303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01012303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf0101230333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012303)) h
theorem e24KC2ThetaAboveLeaf010123100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012310) = true := by
  have h : ((childLL thetaAboveCell01012310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012310) h
theorem e24KC2ThetaAboveLeaf010123101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012310) = true := by
  have h : ((childLH thetaAboveCell01012310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012310) h
theorem e24KC2ThetaAboveLeaf0101231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012310)) h
theorem e24KC2ThetaAboveLeaf0101231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012310)) h
theorem e24KC2ThetaAboveLeaf0101231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012310)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012310)) h
theorem e24KC2ThetaAboveLeaf0101231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012310)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012310)) h
theorem e24KC2ThetaAboveLeaf0101231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012310)) h
theorem e24KC2ThetaAboveLeaf0101231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012310)) h
theorem e24KC2ThetaAboveLeaf0101231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012310)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012310)) h
theorem e24KC2ThetaAboveLeaf0101231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012310)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012310)) h
theorem e24KC2ThetaAboveLeaf010123110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012311) = true := by
  have h : ((childLL thetaAboveCell01012311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012311) h
theorem e24KC2ThetaAboveLeaf010123111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012311) = true := by
  have h : ((childLH thetaAboveCell01012311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012311) h
theorem e24KC2ThetaAboveLeaf0101231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012311)) h
theorem e24KC2ThetaAboveLeaf0101231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012311)) h
theorem e24KC2ThetaAboveLeaf0101231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012311)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012311)) h
theorem e24KC2ThetaAboveLeaf0101231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012311)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012311)) h
theorem e24KC2ThetaAboveLeaf0101231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012311)) h
theorem e24KC2ThetaAboveLeaf0101231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012311)) h
theorem e24KC2ThetaAboveLeaf0101231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012311)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012311)) h
theorem e24KC2ThetaAboveLeaf0101231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012311)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012311)) h
theorem e24KC2ThetaAboveLeaf0101231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01012312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01012312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01012312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01012312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01012312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01012312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01012312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01012312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012312)) h
theorem e24KC2ThetaAboveLeaf0101231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01012313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01012313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01012313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01012313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01012313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01012313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01012313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01012313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01012313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01012313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01012313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01012313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01012313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01012313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01012313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf0101231333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01012313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01012313)) h
theorem e24KC2ThetaAboveLeaf010123200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012320) = true := by
  have h : ((childLL thetaAboveCell01012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012320) h
theorem e24KC2ThetaAboveLeaf010123201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012320) = true := by
  have h : ((childLH thetaAboveCell01012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012320) h
theorem e24KC2ThetaAboveLeaf010123202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01012320) = true := by
  have h : ((childHL thetaAboveCell01012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01012320) h
theorem e24KC2ThetaAboveLeaf010123203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01012320) = true := by
  have h : ((childHH thetaAboveCell01012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01012320) h
theorem e24KC2ThetaAboveLeaf010123210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012321) = true := by
  have h : ((childLL thetaAboveCell01012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012321) h
theorem e24KC2ThetaAboveLeaf010123211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012321) = true := by
  have h : ((childLH thetaAboveCell01012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012321) h
theorem e24KC2ThetaAboveLeaf010123212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01012321) = true := by
  have h : ((childHL thetaAboveCell01012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01012321) h
theorem e24KC2ThetaAboveLeaf010123213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01012321) = true := by
  have h : ((childHH thetaAboveCell01012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01012321) h
theorem e24KC2ThetaAboveLeaf01012322 :
    adaptiveCoverCheck 11 thetaAboveCell01012322 = true := by
  have h : (thetaAboveCell01012322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012322 h
theorem e24KC2ThetaAboveLeaf01012323 :
    adaptiveCoverCheck 11 thetaAboveCell01012323 = true := by
  have h : (thetaAboveCell01012323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012323 h
theorem e24KC2ThetaAboveLeaf010123300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012330) = true := by
  have h : ((childLL thetaAboveCell01012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012330) h
theorem e24KC2ThetaAboveLeaf010123301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012330) = true := by
  have h : ((childLH thetaAboveCell01012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012330) h
theorem e24KC2ThetaAboveLeaf010123302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01012330) = true := by
  have h : ((childHL thetaAboveCell01012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01012330) h
theorem e24KC2ThetaAboveLeaf010123303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01012330) = true := by
  have h : ((childHH thetaAboveCell01012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01012330) h
theorem e24KC2ThetaAboveLeaf010123310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01012331) = true := by
  have h : ((childLL thetaAboveCell01012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01012331) h
theorem e24KC2ThetaAboveLeaf010123311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01012331) = true := by
  have h : ((childLH thetaAboveCell01012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01012331) h
theorem e24KC2ThetaAboveLeaf010123312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01012331) = true := by
  have h : ((childHL thetaAboveCell01012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01012331) h
theorem e24KC2ThetaAboveLeaf010123313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01012331) = true := by
  have h : ((childHH thetaAboveCell01012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01012331) h
theorem e24KC2ThetaAboveLeaf01012332 :
    adaptiveCoverCheck 11 thetaAboveCell01012332 = true := by
  have h : (thetaAboveCell01012332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012332 h
theorem e24KC2ThetaAboveLeaf01012333 :
    adaptiveCoverCheck 11 thetaAboveCell01012333 = true := by
  have h : (thetaAboveCell01012333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01012333 h
theorem e24KC2ThetaAboveLeaf0101300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0101))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0101))) h
theorem e24KC2ThetaAboveLeaf0101301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0101))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0101))) h
theorem e24KC2ThetaAboveLeaf01013020 :
    adaptiveCoverCheck 11 thetaAboveCell01013020 = true := by
  have h : (thetaAboveCell01013020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013020 h
theorem e24KC2ThetaAboveLeaf01013021 :
    adaptiveCoverCheck 11 thetaAboveCell01013021 = true := by
  have h : (thetaAboveCell01013021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013021 h
theorem e24KC2ThetaAboveLeaf01013022 :
    adaptiveCoverCheck 11 thetaAboveCell01013022 = true := by
  have h : (thetaAboveCell01013022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013022 h
theorem e24KC2ThetaAboveLeaf01013023 :
    adaptiveCoverCheck 11 thetaAboveCell01013023 = true := by
  have h : (thetaAboveCell01013023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013023 h
theorem e24KC2ThetaAboveLeaf01013030 :
    adaptiveCoverCheck 11 thetaAboveCell01013030 = true := by
  have h : (thetaAboveCell01013030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013030 h
theorem e24KC2ThetaAboveLeaf01013031 :
    adaptiveCoverCheck 11 thetaAboveCell01013031 = true := by
  have h : (thetaAboveCell01013031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013031 h
theorem e24KC2ThetaAboveLeaf01013032 :
    adaptiveCoverCheck 11 thetaAboveCell01013032 = true := by
  have h : (thetaAboveCell01013032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013032 h
theorem e24KC2ThetaAboveLeaf01013033 :
    adaptiveCoverCheck 11 thetaAboveCell01013033 = true := by
  have h : (thetaAboveCell01013033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013033 h
theorem e24KC2ThetaAboveLeaf0101310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0101))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0101))) h
theorem e24KC2ThetaAboveLeaf0101311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0101))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0101))) h
theorem e24KC2ThetaAboveLeaf01013120 :
    adaptiveCoverCheck 11 thetaAboveCell01013120 = true := by
  have h : (thetaAboveCell01013120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013120 h
theorem e24KC2ThetaAboveLeaf01013121 :
    adaptiveCoverCheck 11 thetaAboveCell01013121 = true := by
  have h : (thetaAboveCell01013121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013121 h
theorem e24KC2ThetaAboveLeaf01013122 :
    adaptiveCoverCheck 11 thetaAboveCell01013122 = true := by
  have h : (thetaAboveCell01013122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013122 h
theorem e24KC2ThetaAboveLeaf01013123 :
    adaptiveCoverCheck 11 thetaAboveCell01013123 = true := by
  have h : (thetaAboveCell01013123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013123 h
theorem e24KC2ThetaAboveLeaf01013130 :
    adaptiveCoverCheck 11 thetaAboveCell01013130 = true := by
  have h : (thetaAboveCell01013130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013130 h
theorem e24KC2ThetaAboveLeaf01013131 :
    adaptiveCoverCheck 11 thetaAboveCell01013131 = true := by
  have h : (thetaAboveCell01013131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013131 h
theorem e24KC2ThetaAboveLeaf01013132 :
    adaptiveCoverCheck 11 thetaAboveCell01013132 = true := by
  have h : (thetaAboveCell01013132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013132 h
theorem e24KC2ThetaAboveLeaf01013133 :
    adaptiveCoverCheck 11 thetaAboveCell01013133 = true := by
  have h : (thetaAboveCell01013133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013133 h
theorem e24KC2ThetaAboveLeaf010132000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013200) = true := by
  have h : ((childLL thetaAboveCell01013200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013200) h
theorem e24KC2ThetaAboveLeaf010132001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013200) = true := by
  have h : ((childLH thetaAboveCell01013200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013200) h
theorem e24KC2ThetaAboveLeaf0101320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013200)) h
theorem e24KC2ThetaAboveLeaf0101320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013200)) h
theorem e24KC2ThetaAboveLeaf0101320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013200)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013200)) h
theorem e24KC2ThetaAboveLeaf0101320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013200)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013200)) h
theorem e24KC2ThetaAboveLeaf0101320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013200)) h
theorem e24KC2ThetaAboveLeaf0101320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013200)) h
theorem e24KC2ThetaAboveLeaf0101320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013200)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013200)) h
theorem e24KC2ThetaAboveLeaf0101320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013200)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013200)) h
theorem e24KC2ThetaAboveLeaf010132010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013201) = true := by
  have h : ((childLL thetaAboveCell01013201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013201) h
theorem e24KC2ThetaAboveLeaf010132011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013201) = true := by
  have h : ((childLH thetaAboveCell01013201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013201) h
theorem e24KC2ThetaAboveLeaf0101320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013201)) h
theorem e24KC2ThetaAboveLeaf0101320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013201)) h
theorem e24KC2ThetaAboveLeaf0101320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013201)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013201)) h
theorem e24KC2ThetaAboveLeaf0101320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013201)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013201)) h
theorem e24KC2ThetaAboveLeaf0101320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013201)) h
theorem e24KC2ThetaAboveLeaf0101320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013201)) h
theorem e24KC2ThetaAboveLeaf0101320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013201)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013201)) h
theorem e24KC2ThetaAboveLeaf0101320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013201)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013201)) h
theorem e24KC2ThetaAboveLeaf0101320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01013202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01013202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01013202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01013202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01013202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01013202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01013202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01013202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013202)) h
theorem e24KC2ThetaAboveLeaf0101320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01013203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01013203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01013203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01013203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01013203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01013203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01013203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01013203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf0101320333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013203)) h
theorem e24KC2ThetaAboveLeaf010132100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013210) = true := by
  have h : ((childLL thetaAboveCell01013210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013210) h
theorem e24KC2ThetaAboveLeaf010132101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013210) = true := by
  have h : ((childLH thetaAboveCell01013210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013210) h
theorem e24KC2ThetaAboveLeaf0101321020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013210)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013210)) h
theorem e24KC2ThetaAboveLeaf0101321021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013210)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013210)) h
theorem e24KC2ThetaAboveLeaf0101321022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013210)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013210)) h
theorem e24KC2ThetaAboveLeaf0101321023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013210)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013210)) h
theorem e24KC2ThetaAboveLeaf0101321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013210)) h
theorem e24KC2ThetaAboveLeaf0101321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013210)) h
theorem e24KC2ThetaAboveLeaf0101321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013210)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013210)) h
theorem e24KC2ThetaAboveLeaf0101321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013210)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013210)) h
theorem e24KC2ThetaAboveLeaf010132110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013211) = true := by
  have h : ((childLL thetaAboveCell01013211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013211) h
theorem e24KC2ThetaAboveLeaf010132111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013211) = true := by
  have h : ((childLH thetaAboveCell01013211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013211) h
theorem e24KC2ThetaAboveLeaf0101321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013211)) h
theorem e24KC2ThetaAboveLeaf0101321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013211)) h
theorem e24KC2ThetaAboveLeaf0101321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013211)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013211)) h
theorem e24KC2ThetaAboveLeaf0101321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013211)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013211)) h
theorem e24KC2ThetaAboveLeaf0101321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013211)) h
theorem e24KC2ThetaAboveLeaf0101321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013211)) h
theorem e24KC2ThetaAboveLeaf0101321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013211)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013211)) h
theorem e24KC2ThetaAboveLeaf0101321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013211)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013211)) h
theorem e24KC2ThetaAboveLeaf0101321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01013212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01013212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01013212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01013212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01013212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01013212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01013212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01013212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013212)) h
theorem e24KC2ThetaAboveLeaf0101321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01013213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01013213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01013213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01013213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01013213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01013213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01013213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01013213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf0101321333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013213)) h
theorem e24KC2ThetaAboveLeaf010132200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013220) = true := by
  have h : ((childLL thetaAboveCell01013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013220) h
theorem e24KC2ThetaAboveLeaf010132201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013220) = true := by
  have h : ((childLH thetaAboveCell01013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013220) h
theorem e24KC2ThetaAboveLeaf010132202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01013220) = true := by
  have h : ((childHL thetaAboveCell01013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01013220) h
theorem e24KC2ThetaAboveLeaf010132203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01013220) = true := by
  have h : ((childHH thetaAboveCell01013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01013220) h
theorem e24KC2ThetaAboveLeaf010132210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013221) = true := by
  have h : ((childLL thetaAboveCell01013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013221) h
theorem e24KC2ThetaAboveLeaf010132211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013221) = true := by
  have h : ((childLH thetaAboveCell01013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013221) h
theorem e24KC2ThetaAboveLeaf010132212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01013221) = true := by
  have h : ((childHL thetaAboveCell01013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01013221) h
theorem e24KC2ThetaAboveLeaf010132213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01013221) = true := by
  have h : ((childHH thetaAboveCell01013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01013221) h
theorem e24KC2ThetaAboveLeaf01013222 :
    adaptiveCoverCheck 11 thetaAboveCell01013222 = true := by
  have h : (thetaAboveCell01013222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013222 h
theorem e24KC2ThetaAboveLeaf01013223 :
    adaptiveCoverCheck 11 thetaAboveCell01013223 = true := by
  have h : (thetaAboveCell01013223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013223 h
theorem e24KC2ThetaAboveLeaf010132300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013230) = true := by
  have h : ((childLL thetaAboveCell01013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013230) h
theorem e24KC2ThetaAboveLeaf010132301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013230) = true := by
  have h : ((childLH thetaAboveCell01013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013230) h
theorem e24KC2ThetaAboveLeaf010132302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01013230) = true := by
  have h : ((childHL thetaAboveCell01013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01013230) h
theorem e24KC2ThetaAboveLeaf010132303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01013230) = true := by
  have h : ((childHH thetaAboveCell01013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01013230) h
theorem e24KC2ThetaAboveLeaf010132310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013231) = true := by
  have h : ((childLL thetaAboveCell01013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013231) h
theorem e24KC2ThetaAboveLeaf010132311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013231) = true := by
  have h : ((childLH thetaAboveCell01013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013231) h
theorem e24KC2ThetaAboveLeaf010132312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01013231) = true := by
  have h : ((childHL thetaAboveCell01013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01013231) h
theorem e24KC2ThetaAboveLeaf010132313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01013231) = true := by
  have h : ((childHH thetaAboveCell01013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01013231) h
theorem e24KC2ThetaAboveLeaf01013232 :
    adaptiveCoverCheck 11 thetaAboveCell01013232 = true := by
  have h : (thetaAboveCell01013232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013232 h
theorem e24KC2ThetaAboveLeaf01013233 :
    adaptiveCoverCheck 11 thetaAboveCell01013233 = true := by
  have h : (thetaAboveCell01013233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013233 h
theorem e24KC2ThetaAboveLeaf010133000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013300) = true := by
  have h : ((childLL thetaAboveCell01013300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013300) h
theorem e24KC2ThetaAboveLeaf010133001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013300) = true := by
  have h : ((childLH thetaAboveCell01013300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013300) h
theorem e24KC2ThetaAboveLeaf0101330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013300)) h
theorem e24KC2ThetaAboveLeaf0101330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013300)) h
theorem e24KC2ThetaAboveLeaf0101330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013300)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013300)) h
theorem e24KC2ThetaAboveLeaf0101330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013300)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013300)) h
theorem e24KC2ThetaAboveLeaf0101330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013300)) h
theorem e24KC2ThetaAboveLeaf0101330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013300)) h
theorem e24KC2ThetaAboveLeaf0101330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013300)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013300)) h
theorem e24KC2ThetaAboveLeaf0101330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013300)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013300)) h

end PartE
end GerverSofa

end

end

end

section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6df5a7a03f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0102 : AngleCell :=
  childHL (childLL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0103 : AngleCell :=
  childHH (childLL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `01013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01013333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01013333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0101)))
/-- Subcell `01102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0110)))
/-- Subcell `01102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0110)))
/-- Subcell `01102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0110)))
/-- Subcell `01102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0110)))
/-- Subcell `01102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0110)))
/-- Subcell `01102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0110)))
/-- Subcell `01102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0110)))
/-- Subcell `01102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0110)))
/-- Subcell `01102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0110)))
/-- Subcell `01102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0110)))
/-- Subcell `01102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0110)))
/-- Subcell `01102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0110)))
/-- Subcell `01102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0110)))
/-- Subcell `01102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0110)))
/-- Subcell `01102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0110)))
/-- Subcell `01102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0110)))
/-- Subcell `01102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0110)))
/-- Subcell `01102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01102333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01102333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0110)))
/-- Subcell `01103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0110)))
/-- Subcell `01103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0110)))
/-- Subcell `01103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0110)))
/-- Subcell `01103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0110)))
/-- Subcell `01103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0110)))
/-- Subcell `01103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0110)))
/-- Subcell `01103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0110)))
/-- Subcell `01103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0110)))
/-- Subcell `01103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0110)))
/-- Subcell `01103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0110)))
/-- Subcell `01103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0110)))
/-- Subcell `01103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0110)))
/-- Subcell `01103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0110)))
/-- Subcell `01103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0110)))
/-- Subcell `01103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0110)))
/-- Subcell `01103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0110)))
/-- Subcell `01103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0110)))

end CertificateCells6df5a7a03f

open CertificateCells6df5a7a03f
theorem e24KC2ThetaAboveLeaf010133010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013301) = true := by
  have h : ((childLL thetaAboveCell01013301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013301) h
theorem e24KC2ThetaAboveLeaf010133011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013301) = true := by
  have h : ((childLH thetaAboveCell01013301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013301) h
theorem e24KC2ThetaAboveLeaf0101330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013301)) h
theorem e24KC2ThetaAboveLeaf0101330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013301)) h
theorem e24KC2ThetaAboveLeaf0101330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013301)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013301)) h
theorem e24KC2ThetaAboveLeaf0101330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013301)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013301)) h
theorem e24KC2ThetaAboveLeaf0101330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013301)) h
theorem e24KC2ThetaAboveLeaf0101330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013301)) h
theorem e24KC2ThetaAboveLeaf0101330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013301)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013301)) h
theorem e24KC2ThetaAboveLeaf0101330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013301)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013301)) h
theorem e24KC2ThetaAboveLeaf0101330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01013302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01013302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01013302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01013302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01013302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01013302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01013302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01013302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013302)) h
theorem e24KC2ThetaAboveLeaf0101330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01013303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01013303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01013303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01013303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01013303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01013303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01013303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01013303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf0101330333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013303)) h
theorem e24KC2ThetaAboveLeaf010133100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013310) = true := by
  have h : ((childLL thetaAboveCell01013310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013310) h
theorem e24KC2ThetaAboveLeaf010133101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013310) = true := by
  have h : ((childLH thetaAboveCell01013310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013310) h
theorem e24KC2ThetaAboveLeaf0101331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013310)) h
theorem e24KC2ThetaAboveLeaf0101331021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013310)) h
theorem e24KC2ThetaAboveLeaf0101331022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013310)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013310)) h
theorem e24KC2ThetaAboveLeaf0101331023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013310)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013310)) h
theorem e24KC2ThetaAboveLeaf0101331030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013310)) h
theorem e24KC2ThetaAboveLeaf0101331031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013310)) h
theorem e24KC2ThetaAboveLeaf0101331032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013310)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013310)) h
theorem e24KC2ThetaAboveLeaf0101331033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013310)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013310)) h
theorem e24KC2ThetaAboveLeaf010133110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013311) = true := by
  have h : ((childLL thetaAboveCell01013311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013311) h
theorem e24KC2ThetaAboveLeaf010133111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013311) = true := by
  have h : ((childLH thetaAboveCell01013311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013311) h
theorem e24KC2ThetaAboveLeaf0101331120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013311)) h
theorem e24KC2ThetaAboveLeaf0101331121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013311)) h
theorem e24KC2ThetaAboveLeaf0101331122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013311)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013311)) h
theorem e24KC2ThetaAboveLeaf0101331123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013311)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013311)) h
theorem e24KC2ThetaAboveLeaf0101331130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013311)) h
theorem e24KC2ThetaAboveLeaf0101331131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013311)) h
theorem e24KC2ThetaAboveLeaf0101331132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013311)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013311)) h
theorem e24KC2ThetaAboveLeaf0101331133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013311)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013311)) h
theorem e24KC2ThetaAboveLeaf0101331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01013312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01013312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01013312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01013312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01013312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01013312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01013312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01013312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013312)) h
theorem e24KC2ThetaAboveLeaf0101331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01013313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01013313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01013313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01013313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01013313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01013313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01013313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01013313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01013313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01013313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01013313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01013313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01013313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01013313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01013313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf0101331333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01013313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01013313)) h
theorem e24KC2ThetaAboveLeaf010133200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013320) = true := by
  have h : ((childLL thetaAboveCell01013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013320) h
theorem e24KC2ThetaAboveLeaf010133201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013320) = true := by
  have h : ((childLH thetaAboveCell01013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013320) h
theorem e24KC2ThetaAboveLeaf010133202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01013320) = true := by
  have h : ((childHL thetaAboveCell01013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01013320) h
theorem e24KC2ThetaAboveLeaf010133203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01013320) = true := by
  have h : ((childHH thetaAboveCell01013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01013320) h
theorem e24KC2ThetaAboveLeaf010133210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013321) = true := by
  have h : ((childLL thetaAboveCell01013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013321) h
theorem e24KC2ThetaAboveLeaf010133211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013321) = true := by
  have h : ((childLH thetaAboveCell01013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013321) h
theorem e24KC2ThetaAboveLeaf010133212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01013321) = true := by
  have h : ((childHL thetaAboveCell01013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01013321) h
theorem e24KC2ThetaAboveLeaf010133213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01013321) = true := by
  have h : ((childHH thetaAboveCell01013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01013321) h
theorem e24KC2ThetaAboveLeaf01013322 :
    adaptiveCoverCheck 11 thetaAboveCell01013322 = true := by
  have h : (thetaAboveCell01013322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013322 h
theorem e24KC2ThetaAboveLeaf01013323 :
    adaptiveCoverCheck 11 thetaAboveCell01013323 = true := by
  have h : (thetaAboveCell01013323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013323 h
theorem e24KC2ThetaAboveLeaf010133300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013330) = true := by
  have h : ((childLL thetaAboveCell01013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013330) h
theorem e24KC2ThetaAboveLeaf010133301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013330) = true := by
  have h : ((childLH thetaAboveCell01013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013330) h
theorem e24KC2ThetaAboveLeaf010133302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01013330) = true := by
  have h : ((childHL thetaAboveCell01013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01013330) h
theorem e24KC2ThetaAboveLeaf010133303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01013330) = true := by
  have h : ((childHH thetaAboveCell01013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01013330) h
theorem e24KC2ThetaAboveLeaf010133310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01013331) = true := by
  have h : ((childLL thetaAboveCell01013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01013331) h
theorem e24KC2ThetaAboveLeaf010133311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01013331) = true := by
  have h : ((childLH thetaAboveCell01013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01013331) h
theorem e24KC2ThetaAboveLeaf010133312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01013331) = true := by
  have h : ((childHL thetaAboveCell01013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01013331) h
theorem e24KC2ThetaAboveLeaf010133313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01013331) = true := by
  have h : ((childHH thetaAboveCell01013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01013331) h
theorem e24KC2ThetaAboveLeaf01013332 :
    adaptiveCoverCheck 11 thetaAboveCell01013332 = true := by
  have h : (thetaAboveCell01013332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013332 h
theorem e24KC2ThetaAboveLeaf01013333 :
    adaptiveCoverCheck 11 thetaAboveCell01013333 = true := by
  have h : (thetaAboveCell01013333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01013333 h
theorem e24KC2ThetaAboveLeaf0102000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0102))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0102))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0102))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0102))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0102))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0102))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0102))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0102))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf010202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0102)) = true := by
  have h : ((childHL (childLL thetaAboveCell0102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0102)) h
theorem e24KC2ThetaAboveLeaf010203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0102)) = true := by
  have h : ((childHH (childLL thetaAboveCell0102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0102)) h
theorem e24KC2ThetaAboveLeaf0102100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0102))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0102))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0102))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0102))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0102))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0102))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0102))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf0102113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0102))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0102)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0102))) h
theorem e24KC2ThetaAboveLeaf010212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0102)) = true := by
  have h : ((childHL (childLH thetaAboveCell0102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0102)) h
theorem e24KC2ThetaAboveLeaf010213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0102)) = true := by
  have h : ((childHH (childLH thetaAboveCell0102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0102)) h
theorem e24KC2ThetaAboveLeaf01022 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0102) = true := by
  have h : ((childHL thetaAboveCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0102) h
theorem e24KC2ThetaAboveLeaf01023 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0102) = true := by
  have h : ((childHH thetaAboveCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0102) h
theorem e24KC2ThetaAboveLeaf0103000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0103))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0103))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0103))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0103))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0103))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0103))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0103))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0103))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf010302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0103)) = true := by
  have h : ((childHL (childLL thetaAboveCell0103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0103)) h
theorem e24KC2ThetaAboveLeaf010303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0103)) = true := by
  have h : ((childHH (childLL thetaAboveCell0103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0103)) h
theorem e24KC2ThetaAboveLeaf0103100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0103))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0103))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0103))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0103))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0103))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0103))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0103))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf0103113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0103))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0103)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0103))) h
theorem e24KC2ThetaAboveLeaf010312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0103)) = true := by
  have h : ((childHL (childLH thetaAboveCell0103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0103)) h
theorem e24KC2ThetaAboveLeaf010313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0103)) = true := by
  have h : ((childHH (childLH thetaAboveCell0103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0103)) h
theorem e24KC2ThetaAboveLeaf01032 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0103) = true := by
  have h : ((childHL thetaAboveCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0103) h
theorem e24KC2ThetaAboveLeaf01033 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0103) = true := by
  have h : ((childHH thetaAboveCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0103) h
theorem e24KC2ThetaAboveLeaf011000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0110)) = true := by
  have h : ((childLL (childLL thetaAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0110)) h
theorem e24KC2ThetaAboveLeaf011001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0110)) = true := by
  have h : ((childLH (childLL thetaAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0110)) h
theorem e24KC2ThetaAboveLeaf011002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0110)) = true := by
  have h : ((childHL (childLL thetaAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0110)) h
theorem e24KC2ThetaAboveLeaf011003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0110)) = true := by
  have h : ((childHH (childLL thetaAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0110)) h
theorem e24KC2ThetaAboveLeaf011010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0110)) = true := by
  have h : ((childLL (childLH thetaAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0110)) h
theorem e24KC2ThetaAboveLeaf011011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0110)) = true := by
  have h : ((childLH (childLH thetaAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0110)) h
theorem e24KC2ThetaAboveLeaf011012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0110)) = true := by
  have h : ((childHL (childLH thetaAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0110)) h
theorem e24KC2ThetaAboveLeaf011013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0110)) = true := by
  have h : ((childHH (childLH thetaAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0110)) h
theorem e24KC2ThetaAboveLeaf0110200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0110))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0110))) h
theorem e24KC2ThetaAboveLeaf0110201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0110))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0110))) h
theorem e24KC2ThetaAboveLeaf01102020 :
    adaptiveCoverCheck 11 thetaAboveCell01102020 = true := by
  have h : (thetaAboveCell01102020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102020 h
theorem e24KC2ThetaAboveLeaf01102021 :
    adaptiveCoverCheck 11 thetaAboveCell01102021 = true := by
  have h : (thetaAboveCell01102021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102021 h
theorem e24KC2ThetaAboveLeaf01102022 :
    adaptiveCoverCheck 11 thetaAboveCell01102022 = true := by
  have h : (thetaAboveCell01102022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102022 h
theorem e24KC2ThetaAboveLeaf01102023 :
    adaptiveCoverCheck 11 thetaAboveCell01102023 = true := by
  have h : (thetaAboveCell01102023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102023 h
theorem e24KC2ThetaAboveLeaf01102030 :
    adaptiveCoverCheck 11 thetaAboveCell01102030 = true := by
  have h : (thetaAboveCell01102030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102030 h
theorem e24KC2ThetaAboveLeaf01102031 :
    adaptiveCoverCheck 11 thetaAboveCell01102031 = true := by
  have h : (thetaAboveCell01102031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102031 h
theorem e24KC2ThetaAboveLeaf01102032 :
    adaptiveCoverCheck 11 thetaAboveCell01102032 = true := by
  have h : (thetaAboveCell01102032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102032 h
theorem e24KC2ThetaAboveLeaf01102033 :
    adaptiveCoverCheck 11 thetaAboveCell01102033 = true := by
  have h : (thetaAboveCell01102033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102033 h
theorem e24KC2ThetaAboveLeaf0110210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0110))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0110))) h
theorem e24KC2ThetaAboveLeaf0110211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0110))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0110))) h
theorem e24KC2ThetaAboveLeaf01102120 :
    adaptiveCoverCheck 11 thetaAboveCell01102120 = true := by
  have h : (thetaAboveCell01102120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102120 h
theorem e24KC2ThetaAboveLeaf01102121 :
    adaptiveCoverCheck 11 thetaAboveCell01102121 = true := by
  have h : (thetaAboveCell01102121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102121 h
theorem e24KC2ThetaAboveLeaf01102122 :
    adaptiveCoverCheck 11 thetaAboveCell01102122 = true := by
  have h : (thetaAboveCell01102122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102122 h
theorem e24KC2ThetaAboveLeaf01102123 :
    adaptiveCoverCheck 11 thetaAboveCell01102123 = true := by
  have h : (thetaAboveCell01102123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102123 h
theorem e24KC2ThetaAboveLeaf01102130 :
    adaptiveCoverCheck 11 thetaAboveCell01102130 = true := by
  have h : (thetaAboveCell01102130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102130 h
theorem e24KC2ThetaAboveLeaf01102131 :
    adaptiveCoverCheck 11 thetaAboveCell01102131 = true := by
  have h : (thetaAboveCell01102131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102131 h
theorem e24KC2ThetaAboveLeaf01102132 :
    adaptiveCoverCheck 11 thetaAboveCell01102132 = true := by
  have h : (thetaAboveCell01102132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102132 h
theorem e24KC2ThetaAboveLeaf01102133 :
    adaptiveCoverCheck 11 thetaAboveCell01102133 = true := by
  have h : (thetaAboveCell01102133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102133 h
theorem e24KC2ThetaAboveLeaf011022000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102200) = true := by
  have h : ((childLL thetaAboveCell01102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102200) h
theorem e24KC2ThetaAboveLeaf011022001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102200) = true := by
  have h : ((childLH thetaAboveCell01102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102200) h
theorem e24KC2ThetaAboveLeaf0110220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102200)) h
theorem e24KC2ThetaAboveLeaf0110220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102200)) h
theorem e24KC2ThetaAboveLeaf0110220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102200)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102200)) h
theorem e24KC2ThetaAboveLeaf0110220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102200)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102200)) h
theorem e24KC2ThetaAboveLeaf0110220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102200)) h
theorem e24KC2ThetaAboveLeaf0110220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102200)) h
theorem e24KC2ThetaAboveLeaf0110220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102200)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102200)) h
theorem e24KC2ThetaAboveLeaf0110220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102200)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102200)) h
theorem e24KC2ThetaAboveLeaf011022010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102201) = true := by
  have h : ((childLL thetaAboveCell01102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102201) h
theorem e24KC2ThetaAboveLeaf011022011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102201) = true := by
  have h : ((childLH thetaAboveCell01102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102201) h
theorem e24KC2ThetaAboveLeaf0110220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102201)) h
theorem e24KC2ThetaAboveLeaf0110220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102201)) h
theorem e24KC2ThetaAboveLeaf0110220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102201)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102201)) h
theorem e24KC2ThetaAboveLeaf0110220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102201)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102201)) h
theorem e24KC2ThetaAboveLeaf0110220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102201)) h
theorem e24KC2ThetaAboveLeaf0110220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102201)) h
theorem e24KC2ThetaAboveLeaf0110220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102201)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102201)) h
theorem e24KC2ThetaAboveLeaf0110220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102201)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102201)) h
theorem e24KC2ThetaAboveLeaf0110220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01102202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01102202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01102202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01102202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01102202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01102202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01102202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01102202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102202)) h
theorem e24KC2ThetaAboveLeaf0110220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01102203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01102203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01102203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01102203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01102203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01102203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01102203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01102203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf0110220333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102203)) h
theorem e24KC2ThetaAboveLeaf011022100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102210) = true := by
  have h : ((childLL thetaAboveCell01102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102210) h
theorem e24KC2ThetaAboveLeaf011022101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102210) = true := by
  have h : ((childLH thetaAboveCell01102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102210) h
theorem e24KC2ThetaAboveLeaf0110221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102210)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102210)) h
theorem e24KC2ThetaAboveLeaf0110221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102210)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102210)) h
theorem e24KC2ThetaAboveLeaf0110221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102210)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102210)) h
theorem e24KC2ThetaAboveLeaf0110221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102210)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102210)) h
theorem e24KC2ThetaAboveLeaf0110221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102210)) h
theorem e24KC2ThetaAboveLeaf0110221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102210)) h
theorem e24KC2ThetaAboveLeaf0110221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102210)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102210)) h
theorem e24KC2ThetaAboveLeaf0110221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102210)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102210)) h
theorem e24KC2ThetaAboveLeaf011022110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102211) = true := by
  have h : ((childLL thetaAboveCell01102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102211) h
theorem e24KC2ThetaAboveLeaf011022111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102211) = true := by
  have h : ((childLH thetaAboveCell01102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102211) h
theorem e24KC2ThetaAboveLeaf0110221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102211)) h
theorem e24KC2ThetaAboveLeaf0110221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102211)) h
theorem e24KC2ThetaAboveLeaf0110221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102211)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102211)) h
theorem e24KC2ThetaAboveLeaf0110221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102211)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102211)) h
theorem e24KC2ThetaAboveLeaf0110221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102211)) h
theorem e24KC2ThetaAboveLeaf0110221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102211)) h
theorem e24KC2ThetaAboveLeaf0110221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102211)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102211)) h
theorem e24KC2ThetaAboveLeaf0110221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102211)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102211)) h
theorem e24KC2ThetaAboveLeaf0110221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01102212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01102212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01102212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01102212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01102212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01102212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01102212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01102212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102212)) h
theorem e24KC2ThetaAboveLeaf0110221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01102213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01102213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01102213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01102213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01102213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01102213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01102213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01102213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf0110221333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102213)) h
theorem e24KC2ThetaAboveLeaf011022200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102220) = true := by
  have h : ((childLL thetaAboveCell01102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102220) h
theorem e24KC2ThetaAboveLeaf011022201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102220) = true := by
  have h : ((childLH thetaAboveCell01102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102220) h
theorem e24KC2ThetaAboveLeaf011022202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01102220) = true := by
  have h : ((childHL thetaAboveCell01102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01102220) h
theorem e24KC2ThetaAboveLeaf011022203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01102220) = true := by
  have h : ((childHH thetaAboveCell01102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01102220) h
theorem e24KC2ThetaAboveLeaf011022210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102221) = true := by
  have h : ((childLL thetaAboveCell01102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102221) h
theorem e24KC2ThetaAboveLeaf011022211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102221) = true := by
  have h : ((childLH thetaAboveCell01102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102221) h
theorem e24KC2ThetaAboveLeaf011022212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01102221) = true := by
  have h : ((childHL thetaAboveCell01102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01102221) h
theorem e24KC2ThetaAboveLeaf011022213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01102221) = true := by
  have h : ((childHH thetaAboveCell01102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01102221) h
theorem e24KC2ThetaAboveLeaf01102222 :
    adaptiveCoverCheck 11 thetaAboveCell01102222 = true := by
  have h : (thetaAboveCell01102222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102222 h
theorem e24KC2ThetaAboveLeaf01102223 :
    adaptiveCoverCheck 11 thetaAboveCell01102223 = true := by
  have h : (thetaAboveCell01102223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102223 h
theorem e24KC2ThetaAboveLeaf011022300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102230) = true := by
  have h : ((childLL thetaAboveCell01102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102230) h
theorem e24KC2ThetaAboveLeaf011022301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102230) = true := by
  have h : ((childLH thetaAboveCell01102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102230) h
theorem e24KC2ThetaAboveLeaf011022302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01102230) = true := by
  have h : ((childHL thetaAboveCell01102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01102230) h
theorem e24KC2ThetaAboveLeaf011022303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01102230) = true := by
  have h : ((childHH thetaAboveCell01102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01102230) h
theorem e24KC2ThetaAboveLeaf011022310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102231) = true := by
  have h : ((childLL thetaAboveCell01102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102231) h
theorem e24KC2ThetaAboveLeaf011022311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102231) = true := by
  have h : ((childLH thetaAboveCell01102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102231) h
theorem e24KC2ThetaAboveLeaf011022312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01102231) = true := by
  have h : ((childHL thetaAboveCell01102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01102231) h
theorem e24KC2ThetaAboveLeaf011022313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01102231) = true := by
  have h : ((childHH thetaAboveCell01102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01102231) h
theorem e24KC2ThetaAboveLeaf01102232 :
    adaptiveCoverCheck 11 thetaAboveCell01102232 = true := by
  have h : (thetaAboveCell01102232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102232 h
theorem e24KC2ThetaAboveLeaf01102233 :
    adaptiveCoverCheck 11 thetaAboveCell01102233 = true := by
  have h : (thetaAboveCell01102233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102233 h
theorem e24KC2ThetaAboveLeaf011023000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102300) = true := by
  have h : ((childLL thetaAboveCell01102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102300) h
theorem e24KC2ThetaAboveLeaf011023001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102300) = true := by
  have h : ((childLH thetaAboveCell01102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102300) h
theorem e24KC2ThetaAboveLeaf0110230020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102300)) h
theorem e24KC2ThetaAboveLeaf0110230021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102300)) h
theorem e24KC2ThetaAboveLeaf0110230022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102300)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102300)) h
theorem e24KC2ThetaAboveLeaf0110230023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102300)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102300)) h
theorem e24KC2ThetaAboveLeaf0110230030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102300)) h
theorem e24KC2ThetaAboveLeaf0110230031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102300)) h
theorem e24KC2ThetaAboveLeaf0110230032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102300)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102300)) h
theorem e24KC2ThetaAboveLeaf0110230033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102300)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102300)) h
theorem e24KC2ThetaAboveLeaf011023010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102301) = true := by
  have h : ((childLL thetaAboveCell01102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102301) h
theorem e24KC2ThetaAboveLeaf011023011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102301) = true := by
  have h : ((childLH thetaAboveCell01102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102301) h
theorem e24KC2ThetaAboveLeaf0110230120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102301)) h
theorem e24KC2ThetaAboveLeaf0110230121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102301)) h
theorem e24KC2ThetaAboveLeaf0110230122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102301)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102301)) h
theorem e24KC2ThetaAboveLeaf0110230123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102301)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102301)) h
theorem e24KC2ThetaAboveLeaf0110230130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102301)) h
theorem e24KC2ThetaAboveLeaf0110230131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102301)) h
theorem e24KC2ThetaAboveLeaf0110230132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102301)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102301)) h
theorem e24KC2ThetaAboveLeaf0110230133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102301)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102301)) h
theorem e24KC2ThetaAboveLeaf0110230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01102302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01102302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01102302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01102302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01102302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01102302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01102302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01102302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102302)) h
theorem e24KC2ThetaAboveLeaf0110230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01102303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01102303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01102303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01102303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01102303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01102303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01102303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01102303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf0110230333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102303)) h
theorem e24KC2ThetaAboveLeaf011023100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102310) = true := by
  have h : ((childLL thetaAboveCell01102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102310) h
theorem e24KC2ThetaAboveLeaf011023101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102310) = true := by
  have h : ((childLH thetaAboveCell01102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102310) h
theorem e24KC2ThetaAboveLeaf0110231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102310)) h
theorem e24KC2ThetaAboveLeaf0110231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102310)) h
theorem e24KC2ThetaAboveLeaf0110231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102310)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102310)) h
theorem e24KC2ThetaAboveLeaf0110231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102310)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102310)) h
theorem e24KC2ThetaAboveLeaf0110231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102310)) h
theorem e24KC2ThetaAboveLeaf0110231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102310)) h
theorem e24KC2ThetaAboveLeaf0110231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102310)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102310)) h
theorem e24KC2ThetaAboveLeaf0110231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102310)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102310)) h
theorem e24KC2ThetaAboveLeaf011023110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102311) = true := by
  have h : ((childLL thetaAboveCell01102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102311) h
theorem e24KC2ThetaAboveLeaf011023111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102311) = true := by
  have h : ((childLH thetaAboveCell01102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102311) h
theorem e24KC2ThetaAboveLeaf0110231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102311)) h
theorem e24KC2ThetaAboveLeaf0110231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102311)) h
theorem e24KC2ThetaAboveLeaf0110231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102311)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102311)) h
theorem e24KC2ThetaAboveLeaf0110231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102311)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102311)) h
theorem e24KC2ThetaAboveLeaf0110231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102311)) h
theorem e24KC2ThetaAboveLeaf0110231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102311)) h
theorem e24KC2ThetaAboveLeaf0110231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102311)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102311)) h
theorem e24KC2ThetaAboveLeaf0110231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102311)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102311)) h
theorem e24KC2ThetaAboveLeaf0110231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01102312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01102312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01102312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01102312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01102312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01102312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01102312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01102312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102312)) h
theorem e24KC2ThetaAboveLeaf0110231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01102313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01102313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01102313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01102313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01102313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01102313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01102313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01102313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01102313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01102313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01102313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01102313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01102313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01102313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01102313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf0110231333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01102313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01102313)) h
theorem e24KC2ThetaAboveLeaf011023200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102320) = true := by
  have h : ((childLL thetaAboveCell01102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102320) h
theorem e24KC2ThetaAboveLeaf011023201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102320) = true := by
  have h : ((childLH thetaAboveCell01102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102320) h
theorem e24KC2ThetaAboveLeaf011023202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01102320) = true := by
  have h : ((childHL thetaAboveCell01102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01102320) h
theorem e24KC2ThetaAboveLeaf011023203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01102320) = true := by
  have h : ((childHH thetaAboveCell01102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01102320) h
theorem e24KC2ThetaAboveLeaf011023210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102321) = true := by
  have h : ((childLL thetaAboveCell01102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102321) h
theorem e24KC2ThetaAboveLeaf011023211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102321) = true := by
  have h : ((childLH thetaAboveCell01102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102321) h
theorem e24KC2ThetaAboveLeaf011023212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01102321) = true := by
  have h : ((childHL thetaAboveCell01102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01102321) h
theorem e24KC2ThetaAboveLeaf011023213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01102321) = true := by
  have h : ((childHH thetaAboveCell01102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01102321) h
theorem e24KC2ThetaAboveLeaf01102322 :
    adaptiveCoverCheck 11 thetaAboveCell01102322 = true := by
  have h : (thetaAboveCell01102322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102322 h
theorem e24KC2ThetaAboveLeaf01102323 :
    adaptiveCoverCheck 11 thetaAboveCell01102323 = true := by
  have h : (thetaAboveCell01102323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102323 h
theorem e24KC2ThetaAboveLeaf011023300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102330) = true := by
  have h : ((childLL thetaAboveCell01102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102330) h
theorem e24KC2ThetaAboveLeaf011023301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102330) = true := by
  have h : ((childLH thetaAboveCell01102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102330) h
theorem e24KC2ThetaAboveLeaf011023302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01102330) = true := by
  have h : ((childHL thetaAboveCell01102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01102330) h
theorem e24KC2ThetaAboveLeaf011023303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01102330) = true := by
  have h : ((childHH thetaAboveCell01102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01102330) h
theorem e24KC2ThetaAboveLeaf011023310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01102331) = true := by
  have h : ((childLL thetaAboveCell01102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01102331) h
theorem e24KC2ThetaAboveLeaf011023311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01102331) = true := by
  have h : ((childLH thetaAboveCell01102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01102331) h
theorem e24KC2ThetaAboveLeaf011023312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01102331) = true := by
  have h : ((childHL thetaAboveCell01102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01102331) h
theorem e24KC2ThetaAboveLeaf011023313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01102331) = true := by
  have h : ((childHH thetaAboveCell01102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01102331) h
theorem e24KC2ThetaAboveLeaf01102332 :
    adaptiveCoverCheck 11 thetaAboveCell01102332 = true := by
  have h : (thetaAboveCell01102332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102332 h
theorem e24KC2ThetaAboveLeaf01102333 :
    adaptiveCoverCheck 11 thetaAboveCell01102333 = true := by
  have h : (thetaAboveCell01102333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01102333 h
theorem e24KC2ThetaAboveLeaf0110300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0110))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0110))) h
theorem e24KC2ThetaAboveLeaf0110301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0110))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0110))) h
theorem e24KC2ThetaAboveLeaf01103020 :
    adaptiveCoverCheck 11 thetaAboveCell01103020 = true := by
  have h : (thetaAboveCell01103020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103020 h
theorem e24KC2ThetaAboveLeaf01103021 :
    adaptiveCoverCheck 11 thetaAboveCell01103021 = true := by
  have h : (thetaAboveCell01103021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103021 h
theorem e24KC2ThetaAboveLeaf01103022 :
    adaptiveCoverCheck 11 thetaAboveCell01103022 = true := by
  have h : (thetaAboveCell01103022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103022 h
theorem e24KC2ThetaAboveLeaf01103023 :
    adaptiveCoverCheck 11 thetaAboveCell01103023 = true := by
  have h : (thetaAboveCell01103023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103023 h
theorem e24KC2ThetaAboveLeaf01103030 :
    adaptiveCoverCheck 11 thetaAboveCell01103030 = true := by
  have h : (thetaAboveCell01103030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103030 h
theorem e24KC2ThetaAboveLeaf01103031 :
    adaptiveCoverCheck 11 thetaAboveCell01103031 = true := by
  have h : (thetaAboveCell01103031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103031 h
theorem e24KC2ThetaAboveLeaf01103032 :
    adaptiveCoverCheck 11 thetaAboveCell01103032 = true := by
  have h : (thetaAboveCell01103032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103032 h
theorem e24KC2ThetaAboveLeaf01103033 :
    adaptiveCoverCheck 11 thetaAboveCell01103033 = true := by
  have h : (thetaAboveCell01103033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103033 h
theorem e24KC2ThetaAboveLeaf0110310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0110))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0110))) h
theorem e24KC2ThetaAboveLeaf0110311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0110))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0110))) h
theorem e24KC2ThetaAboveLeaf01103120 :
    adaptiveCoverCheck 11 thetaAboveCell01103120 = true := by
  have h : (thetaAboveCell01103120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103120 h
theorem e24KC2ThetaAboveLeaf01103121 :
    adaptiveCoverCheck 11 thetaAboveCell01103121 = true := by
  have h : (thetaAboveCell01103121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103121 h
theorem e24KC2ThetaAboveLeaf01103122 :
    adaptiveCoverCheck 11 thetaAboveCell01103122 = true := by
  have h : (thetaAboveCell01103122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103122 h
theorem e24KC2ThetaAboveLeaf01103123 :
    adaptiveCoverCheck 11 thetaAboveCell01103123 = true := by
  have h : (thetaAboveCell01103123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103123 h
theorem e24KC2ThetaAboveLeaf01103130 :
    adaptiveCoverCheck 11 thetaAboveCell01103130 = true := by
  have h : (thetaAboveCell01103130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103130 h
theorem e24KC2ThetaAboveLeaf01103131 :
    adaptiveCoverCheck 11 thetaAboveCell01103131 = true := by
  have h : (thetaAboveCell01103131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103131 h
theorem e24KC2ThetaAboveLeaf01103132 :
    adaptiveCoverCheck 11 thetaAboveCell01103132 = true := by
  have h : (thetaAboveCell01103132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103132 h
theorem e24KC2ThetaAboveLeaf01103133 :
    adaptiveCoverCheck 11 thetaAboveCell01103133 = true := by
  have h : (thetaAboveCell01103133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103133 h
theorem e24KC2ThetaAboveLeaf011032000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103200) = true := by
  have h : ((childLL thetaAboveCell01103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103200) h
theorem e24KC2ThetaAboveLeaf011032001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103200) = true := by
  have h : ((childLH thetaAboveCell01103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103200) h
theorem e24KC2ThetaAboveLeaf0110320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103200)) h
theorem e24KC2ThetaAboveLeaf0110320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103200)) h
theorem e24KC2ThetaAboveLeaf0110320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103200)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103200)) h
theorem e24KC2ThetaAboveLeaf0110320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103200)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103200)) h
theorem e24KC2ThetaAboveLeaf0110320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103200)) h
theorem e24KC2ThetaAboveLeaf0110320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103200)) h
theorem e24KC2ThetaAboveLeaf0110320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103200)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103200)) h
theorem e24KC2ThetaAboveLeaf0110320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103200)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103200)) h
theorem e24KC2ThetaAboveLeaf011032010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103201) = true := by
  have h : ((childLL thetaAboveCell01103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103201) h
theorem e24KC2ThetaAboveLeaf011032011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103201) = true := by
  have h : ((childLH thetaAboveCell01103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103201) h
theorem e24KC2ThetaAboveLeaf0110320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103201)) h
theorem e24KC2ThetaAboveLeaf0110320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103201)) h
theorem e24KC2ThetaAboveLeaf0110320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103201)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103201)) h
theorem e24KC2ThetaAboveLeaf0110320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103201)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103201)) h
theorem e24KC2ThetaAboveLeaf0110320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103201)) h
theorem e24KC2ThetaAboveLeaf0110320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103201)) h
theorem e24KC2ThetaAboveLeaf0110320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103201)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103201)) h
theorem e24KC2ThetaAboveLeaf0110320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103201)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103201)) h
theorem e24KC2ThetaAboveLeaf0110320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103202)) h
theorem e24KC2ThetaAboveLeaf0110320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf0110320333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103203)) h
theorem e24KC2ThetaAboveLeaf011032100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103210) = true := by
  have h : ((childLL thetaAboveCell01103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103210) h
theorem e24KC2ThetaAboveLeaf011032101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103210) = true := by
  have h : ((childLH thetaAboveCell01103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103210) h
theorem e24KC2ThetaAboveLeaf0110321020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103210)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103210)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103210)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103210)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103210)) h

end PartE
end GerverSofa

end

end

end
