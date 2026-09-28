/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT665600016`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsce54db6860

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1023 : AngleCell :=
  childHH (childHL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1030 : AngleCell :=
  childLL (childHH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1031 : AngleCell :=
  childLH (childHH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1032 : AngleCell :=
  childHL (childHH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1033 : AngleCell :=
  childHH (childHH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1102 : AngleCell :=
  childHL (childLL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1103 : AngleCell :=
  childHH (childLL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11000320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11000320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell1100)))
/-- Subcell `11000321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11000321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell1100)))
/-- Subcell `11000322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11000322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell1100)))
/-- Subcell `11000323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11000323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell1100)))
/-- Subcell `11000330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11000330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell1100)))
/-- Subcell `11000331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11000331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell1100)))
/-- Subcell `11000332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11000332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell1100)))
/-- Subcell `11000333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11000333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell1100)))
/-- Subcell `11001220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell1100)))
/-- Subcell `11001221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell1100)))
/-- Subcell `11001222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell1100)))
/-- Subcell `11001223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell1100)))
/-- Subcell `11001230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell1100)))
/-- Subcell `11001231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell1100)))
/-- Subcell `11001232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell1100)))
/-- Subcell `11001233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell1100)))
/-- Subcell `11001320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell1100)))
/-- Subcell `11001321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell1100)))
/-- Subcell `11001322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell1100)))
/-- Subcell `11001323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell1100)))
/-- Subcell `11001330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell1100)))
/-- Subcell `11001331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell1100)))
/-- Subcell `11001332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell1100)))
/-- Subcell `11001333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11001333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell1100)))
/-- Subcell `11002000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell1100)))
/-- Subcell `11002100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11002133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1100)))
/-- Subcell `11003000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1100)))
/-- Subcell `11003100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1100)))
/-- Subcell `11003300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1100)))
/-- Subcell `11003301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1100)))
/-- Subcell `11003302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaBelowCell1100)))
/-- Subcell `11003303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaBelowCell1100)))
/-- Subcell `11003310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1100)))
/-- Subcell `11003311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1100)))
/-- Subcell `11003312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1100)))
/-- Subcell `11003313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1100)))
/-- Subcell `11010220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11010220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell1101)))
/-- Subcell `11010221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11010221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell1101)))
/-- Subcell `11010222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11010222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell1101)))
/-- Subcell `11010223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11010223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell1101)))
/-- Subcell `11010230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11010230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell1101)))
/-- Subcell `11010231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11010231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell1101)))
/-- Subcell `11010232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11010232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell1101)))
/-- Subcell `11010233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11010233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell1101)))
/-- Subcell `11012000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell1101)))
/-- Subcell `11012100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1101)))
/-- Subcell `11012201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1101)))
/-- Subcell `11012202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaBelowCell1101)))
/-- Subcell `11012203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaBelowCell1101)))
/-- Subcell `11012210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1101)))
/-- Subcell `11012211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1101)))
/-- Subcell `11012212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaBelowCell1101)))
/-- Subcell `11012213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaBelowCell1101)))
/-- Subcell `11012300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaBelowCell1101)))
/-- Subcell `11012301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaBelowCell1101)))
/-- Subcell `11012302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaBelowCell1101)))
/-- Subcell `11012303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaBelowCell1101)))
/-- Subcell `11012310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaBelowCell1101)))
/-- Subcell `11012311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaBelowCell1101)))
/-- Subcell `11012312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaBelowCell1101)))
/-- Subcell `11012313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaBelowCell1101)))
/-- Subcell `11013000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaBelowCell1101)))
/-- Subcell `11013201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaBelowCell1101)))
/-- Subcell `11013202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaBelowCell1101)))
/-- Subcell `11013203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaBelowCell1101)))
/-- Subcell `11013210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1101)))
/-- Subcell `11013211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1101)))
/-- Subcell `11013212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaBelowCell1101)))
/-- Subcell `11013213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaBelowCell1101)))
/-- Subcell `11013300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1101)))
/-- Subcell `11013301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1101)))
/-- Subcell `11013302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaBelowCell1101)))
/-- Subcell `11013303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaBelowCell1101)))
/-- Subcell `11013310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1101)))
/-- Subcell `11013311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1101)))
/-- Subcell `11013312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1101)))
/-- Subcell `11013313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1101)))
/-- Subcell `11102000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11103000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1110)))

end CertificateCellsce54db6860

open CertificateCellsce54db6860
theorem e24KC2ThetaBelowLeaf1023 :
    adaptiveCoverCheck 14 thetaBelowCell1023 = true := by
  have h : (thetaBelowCell1023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1023 h
theorem e24KC2ThetaBelowLeaf1030 :
    adaptiveCoverCheck 14 thetaBelowCell1030 = true := by
  have h : (thetaBelowCell1030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1030 h
theorem e24KC2ThetaBelowLeaf1031 :
    adaptiveCoverCheck 14 thetaBelowCell1031 = true := by
  have h : (thetaBelowCell1031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1031 h
theorem e24KC2ThetaBelowLeaf1032 :
    adaptiveCoverCheck 14 thetaBelowCell1032 = true := by
  have h : (thetaBelowCell1032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1032 h
theorem e24KC2ThetaBelowLeaf1033 :
    adaptiveCoverCheck 14 thetaBelowCell1033 = true := by
  have h : (thetaBelowCell1033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1033 h
theorem e24KC2ThetaBelowLeaf110000 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1100)) = true := by
  have h : ((childLL (childLL thetaBelowCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1100)) h
theorem e24KC2ThetaBelowLeaf110001 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1100)) = true := by
  have h : ((childLH (childLL thetaBelowCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1100)) h
theorem e24KC2ThetaBelowLeaf1100020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1100))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1100))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1100))) = true := by
  have h : ((childHL (childHL (childLL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1100))) = true := by
  have h : ((childHH (childHL (childLL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1100))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1100))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf11000320 :
    adaptiveCoverCheck 10 thetaBelowCell11000320 = true := by
  have h : (thetaBelowCell11000320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11000320 h
theorem e24KC2ThetaBelowLeaf11000321 :
    adaptiveCoverCheck 10 thetaBelowCell11000321 = true := by
  have h : (thetaBelowCell11000321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11000321 h
theorem e24KC2ThetaBelowLeaf11000322 :
    adaptiveCoverCheck 10 thetaBelowCell11000322 = true := by
  have h : (thetaBelowCell11000322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11000322 h
theorem e24KC2ThetaBelowLeaf11000323 :
    adaptiveCoverCheck 10 thetaBelowCell11000323 = true := by
  have h : (thetaBelowCell11000323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11000323 h
theorem e24KC2ThetaBelowLeaf11000330 :
    adaptiveCoverCheck 10 thetaBelowCell11000330 = true := by
  have h : (thetaBelowCell11000330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11000330 h
theorem e24KC2ThetaBelowLeaf11000331 :
    adaptiveCoverCheck 10 thetaBelowCell11000331 = true := by
  have h : (thetaBelowCell11000331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11000331 h
theorem e24KC2ThetaBelowLeaf11000332 :
    adaptiveCoverCheck 10 thetaBelowCell11000332 = true := by
  have h : (thetaBelowCell11000332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11000332 h
theorem e24KC2ThetaBelowLeaf11000333 :
    adaptiveCoverCheck 10 thetaBelowCell11000333 = true := by
  have h : (thetaBelowCell11000333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11000333 h
theorem e24KC2ThetaBelowLeaf110010 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1100)) = true := by
  have h : ((childLL (childLH thetaBelowCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1100)) h
theorem e24KC2ThetaBelowLeaf110011 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1100)) = true := by
  have h : ((childLH (childLH thetaBelowCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1100)) h
theorem e24KC2ThetaBelowLeaf1100120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1100))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1100))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf11001220 :
    adaptiveCoverCheck 10 thetaBelowCell11001220 = true := by
  have h : (thetaBelowCell11001220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001220 h
theorem e24KC2ThetaBelowLeaf11001221 :
    adaptiveCoverCheck 10 thetaBelowCell11001221 = true := by
  have h : (thetaBelowCell11001221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001221 h
theorem e24KC2ThetaBelowLeaf11001222 :
    adaptiveCoverCheck 10 thetaBelowCell11001222 = true := by
  have h : (thetaBelowCell11001222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001222 h
theorem e24KC2ThetaBelowLeaf11001223 :
    adaptiveCoverCheck 10 thetaBelowCell11001223 = true := by
  have h : (thetaBelowCell11001223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001223 h
theorem e24KC2ThetaBelowLeaf11001230 :
    adaptiveCoverCheck 10 thetaBelowCell11001230 = true := by
  have h : (thetaBelowCell11001230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001230 h
theorem e24KC2ThetaBelowLeaf11001231 :
    adaptiveCoverCheck 10 thetaBelowCell11001231 = true := by
  have h : (thetaBelowCell11001231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001231 h
theorem e24KC2ThetaBelowLeaf11001232 :
    adaptiveCoverCheck 10 thetaBelowCell11001232 = true := by
  have h : (thetaBelowCell11001232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001232 h
theorem e24KC2ThetaBelowLeaf11001233 :
    adaptiveCoverCheck 10 thetaBelowCell11001233 = true := by
  have h : (thetaBelowCell11001233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001233 h
theorem e24KC2ThetaBelowLeaf1100130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1100))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1100))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf11001320 :
    adaptiveCoverCheck 10 thetaBelowCell11001320 = true := by
  have h : (thetaBelowCell11001320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001320 h
theorem e24KC2ThetaBelowLeaf11001321 :
    adaptiveCoverCheck 10 thetaBelowCell11001321 = true := by
  have h : (thetaBelowCell11001321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001321 h
theorem e24KC2ThetaBelowLeaf11001322 :
    adaptiveCoverCheck 10 thetaBelowCell11001322 = true := by
  have h : (thetaBelowCell11001322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001322 h
theorem e24KC2ThetaBelowLeaf11001323 :
    adaptiveCoverCheck 10 thetaBelowCell11001323 = true := by
  have h : (thetaBelowCell11001323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001323 h
theorem e24KC2ThetaBelowLeaf11001330 :
    adaptiveCoverCheck 10 thetaBelowCell11001330 = true := by
  have h : (thetaBelowCell11001330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001330 h
theorem e24KC2ThetaBelowLeaf11001331 :
    adaptiveCoverCheck 10 thetaBelowCell11001331 = true := by
  have h : (thetaBelowCell11001331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001331 h
theorem e24KC2ThetaBelowLeaf11001332 :
    adaptiveCoverCheck 10 thetaBelowCell11001332 = true := by
  have h : (thetaBelowCell11001332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001332 h
theorem e24KC2ThetaBelowLeaf11001333 :
    adaptiveCoverCheck 10 thetaBelowCell11001333 = true := by
  have h : (thetaBelowCell11001333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11001333 h
theorem e24KC2ThetaBelowLeaf11002000 :
    adaptiveCoverCheck 10 thetaBelowCell11002000 = true := by
  have h : (thetaBelowCell11002000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002000 h
theorem e24KC2ThetaBelowLeaf11002001 :
    adaptiveCoverCheck 10 thetaBelowCell11002001 = true := by
  have h : (thetaBelowCell11002001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002001 h
theorem e24KC2ThetaBelowLeaf11002002 :
    adaptiveCoverCheck 10 thetaBelowCell11002002 = true := by
  have h : (thetaBelowCell11002002).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002002 h
theorem e24KC2ThetaBelowLeaf11002003 :
    adaptiveCoverCheck 10 thetaBelowCell11002003 = true := by
  have h : (thetaBelowCell11002003).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002003 h
theorem e24KC2ThetaBelowLeaf11002010 :
    adaptiveCoverCheck 10 thetaBelowCell11002010 = true := by
  have h : (thetaBelowCell11002010).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002010 h
theorem e24KC2ThetaBelowLeaf11002011 :
    adaptiveCoverCheck 10 thetaBelowCell11002011 = true := by
  have h : (thetaBelowCell11002011).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002011 h
theorem e24KC2ThetaBelowLeaf11002012 :
    adaptiveCoverCheck 10 thetaBelowCell11002012 = true := by
  have h : (thetaBelowCell11002012).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002012 h
theorem e24KC2ThetaBelowLeaf11002013 :
    adaptiveCoverCheck 10 thetaBelowCell11002013 = true := by
  have h : (thetaBelowCell11002013).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002013 h
theorem e24KC2ThetaBelowLeaf11002020 :
    adaptiveCoverCheck 10 thetaBelowCell11002020 = true := by
  have h : (thetaBelowCell11002020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002020 h
theorem e24KC2ThetaBelowLeaf11002021 :
    adaptiveCoverCheck 10 thetaBelowCell11002021 = true := by
  have h : (thetaBelowCell11002021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002021 h
theorem e24KC2ThetaBelowLeaf11002022 :
    adaptiveCoverCheck 10 thetaBelowCell11002022 = true := by
  have h : (thetaBelowCell11002022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002022 h
theorem e24KC2ThetaBelowLeaf11002023 :
    adaptiveCoverCheck 10 thetaBelowCell11002023 = true := by
  have h : (thetaBelowCell11002023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002023 h
theorem e24KC2ThetaBelowLeaf11002030 :
    adaptiveCoverCheck 10 thetaBelowCell11002030 = true := by
  have h : (thetaBelowCell11002030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002030 h
theorem e24KC2ThetaBelowLeaf11002031 :
    adaptiveCoverCheck 10 thetaBelowCell11002031 = true := by
  have h : (thetaBelowCell11002031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002031 h
theorem e24KC2ThetaBelowLeaf11002032 :
    adaptiveCoverCheck 10 thetaBelowCell11002032 = true := by
  have h : (thetaBelowCell11002032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002032 h
theorem e24KC2ThetaBelowLeaf11002033 :
    adaptiveCoverCheck 10 thetaBelowCell11002033 = true := by
  have h : (thetaBelowCell11002033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002033 h
theorem e24KC2ThetaBelowLeaf11002100 :
    adaptiveCoverCheck 10 thetaBelowCell11002100 = true := by
  have h : (thetaBelowCell11002100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002100 h
theorem e24KC2ThetaBelowLeaf11002101 :
    adaptiveCoverCheck 10 thetaBelowCell11002101 = true := by
  have h : (thetaBelowCell11002101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002101 h
theorem e24KC2ThetaBelowLeaf11002102 :
    adaptiveCoverCheck 10 thetaBelowCell11002102 = true := by
  have h : (thetaBelowCell11002102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002102 h
theorem e24KC2ThetaBelowLeaf11002103 :
    adaptiveCoverCheck 10 thetaBelowCell11002103 = true := by
  have h : (thetaBelowCell11002103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002103 h
theorem e24KC2ThetaBelowLeaf11002110 :
    adaptiveCoverCheck 10 thetaBelowCell11002110 = true := by
  have h : (thetaBelowCell11002110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002110 h
theorem e24KC2ThetaBelowLeaf11002111 :
    adaptiveCoverCheck 10 thetaBelowCell11002111 = true := by
  have h : (thetaBelowCell11002111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002111 h
theorem e24KC2ThetaBelowLeaf11002112 :
    adaptiveCoverCheck 10 thetaBelowCell11002112 = true := by
  have h : (thetaBelowCell11002112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002112 h
theorem e24KC2ThetaBelowLeaf11002113 :
    adaptiveCoverCheck 10 thetaBelowCell11002113 = true := by
  have h : (thetaBelowCell11002113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002113 h
theorem e24KC2ThetaBelowLeaf11002120 :
    adaptiveCoverCheck 10 thetaBelowCell11002120 = true := by
  have h : (thetaBelowCell11002120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002120 h
theorem e24KC2ThetaBelowLeaf11002121 :
    adaptiveCoverCheck 10 thetaBelowCell11002121 = true := by
  have h : (thetaBelowCell11002121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002121 h
theorem e24KC2ThetaBelowLeaf11002122 :
    adaptiveCoverCheck 10 thetaBelowCell11002122 = true := by
  have h : (thetaBelowCell11002122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002122 h
theorem e24KC2ThetaBelowLeaf11002123 :
    adaptiveCoverCheck 10 thetaBelowCell11002123 = true := by
  have h : (thetaBelowCell11002123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002123 h
theorem e24KC2ThetaBelowLeaf11002130 :
    adaptiveCoverCheck 10 thetaBelowCell11002130 = true := by
  have h : (thetaBelowCell11002130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002130 h
theorem e24KC2ThetaBelowLeaf11002131 :
    adaptiveCoverCheck 10 thetaBelowCell11002131 = true := by
  have h : (thetaBelowCell11002131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002131 h
theorem e24KC2ThetaBelowLeaf11002132 :
    adaptiveCoverCheck 10 thetaBelowCell11002132 = true := by
  have h : (thetaBelowCell11002132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002132 h
theorem e24KC2ThetaBelowLeaf11002133 :
    adaptiveCoverCheck 10 thetaBelowCell11002133 = true := by
  have h : (thetaBelowCell11002133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11002133 h
theorem e24KC2ThetaBelowLeaf1100220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1100))) = true := by
  have h : ((childLL (childHL (childHL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1100))) = true := by
  have h : ((childLH (childHL (childHL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL thetaBelowCell1100))) = true := by
  have h : ((childHL (childHL (childHL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL thetaBelowCell1100))) = true := by
  have h : ((childHH (childHL (childHL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1100))) = true := by
  have h : ((childLL (childHH (childHL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1100))) = true := by
  have h : ((childLH (childHH (childHL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL thetaBelowCell1100))) = true := by
  have h : ((childHL (childHH (childHL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL thetaBelowCell1100))) = true := by
  have h : ((childHH (childHH (childHL thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf11003000 :
    adaptiveCoverCheck 10 thetaBelowCell11003000 = true := by
  have h : (thetaBelowCell11003000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003000 h
theorem e24KC2ThetaBelowLeaf11003001 :
    adaptiveCoverCheck 10 thetaBelowCell11003001 = true := by
  have h : (thetaBelowCell11003001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003001 h
theorem e24KC2ThetaBelowLeaf11003002 :
    adaptiveCoverCheck 10 thetaBelowCell11003002 = true := by
  have h : (thetaBelowCell11003002).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003002 h
theorem e24KC2ThetaBelowLeaf11003003 :
    adaptiveCoverCheck 10 thetaBelowCell11003003 = true := by
  have h : (thetaBelowCell11003003).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003003 h
theorem e24KC2ThetaBelowLeaf11003010 :
    adaptiveCoverCheck 10 thetaBelowCell11003010 = true := by
  have h : (thetaBelowCell11003010).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003010 h
theorem e24KC2ThetaBelowLeaf11003011 :
    adaptiveCoverCheck 10 thetaBelowCell11003011 = true := by
  have h : (thetaBelowCell11003011).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003011 h
theorem e24KC2ThetaBelowLeaf11003012 :
    adaptiveCoverCheck 10 thetaBelowCell11003012 = true := by
  have h : (thetaBelowCell11003012).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003012 h
theorem e24KC2ThetaBelowLeaf11003013 :
    adaptiveCoverCheck 10 thetaBelowCell11003013 = true := by
  have h : (thetaBelowCell11003013).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003013 h
theorem e24KC2ThetaBelowLeaf11003020 :
    adaptiveCoverCheck 10 thetaBelowCell11003020 = true := by
  have h : (thetaBelowCell11003020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003020 h
theorem e24KC2ThetaBelowLeaf11003021 :
    adaptiveCoverCheck 10 thetaBelowCell11003021 = true := by
  have h : (thetaBelowCell11003021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003021 h
theorem e24KC2ThetaBelowLeaf11003022 :
    adaptiveCoverCheck 10 thetaBelowCell11003022 = true := by
  have h : (thetaBelowCell11003022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003022 h
theorem e24KC2ThetaBelowLeaf11003023 :
    adaptiveCoverCheck 10 thetaBelowCell11003023 = true := by
  have h : (thetaBelowCell11003023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003023 h
theorem e24KC2ThetaBelowLeaf11003030 :
    adaptiveCoverCheck 10 thetaBelowCell11003030 = true := by
  have h : (thetaBelowCell11003030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003030 h
theorem e24KC2ThetaBelowLeaf11003031 :
    adaptiveCoverCheck 10 thetaBelowCell11003031 = true := by
  have h : (thetaBelowCell11003031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003031 h
theorem e24KC2ThetaBelowLeaf11003032 :
    adaptiveCoverCheck 10 thetaBelowCell11003032 = true := by
  have h : (thetaBelowCell11003032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003032 h
theorem e24KC2ThetaBelowLeaf11003033 :
    adaptiveCoverCheck 10 thetaBelowCell11003033 = true := by
  have h : (thetaBelowCell11003033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003033 h
theorem e24KC2ThetaBelowLeaf11003100 :
    adaptiveCoverCheck 10 thetaBelowCell11003100 = true := by
  have h : (thetaBelowCell11003100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003100 h
theorem e24KC2ThetaBelowLeaf11003101 :
    adaptiveCoverCheck 10 thetaBelowCell11003101 = true := by
  have h : (thetaBelowCell11003101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003101 h
theorem e24KC2ThetaBelowLeaf11003102 :
    adaptiveCoverCheck 10 thetaBelowCell11003102 = true := by
  have h : (thetaBelowCell11003102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003102 h
theorem e24KC2ThetaBelowLeaf11003103 :
    adaptiveCoverCheck 10 thetaBelowCell11003103 = true := by
  have h : (thetaBelowCell11003103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003103 h
theorem e24KC2ThetaBelowLeaf11003110 :
    adaptiveCoverCheck 10 thetaBelowCell11003110 = true := by
  have h : (thetaBelowCell11003110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003110 h
theorem e24KC2ThetaBelowLeaf11003111 :
    adaptiveCoverCheck 10 thetaBelowCell11003111 = true := by
  have h : (thetaBelowCell11003111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003111 h
theorem e24KC2ThetaBelowLeaf11003112 :
    adaptiveCoverCheck 10 thetaBelowCell11003112 = true := by
  have h : (thetaBelowCell11003112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003112 h
theorem e24KC2ThetaBelowLeaf11003113 :
    adaptiveCoverCheck 10 thetaBelowCell11003113 = true := by
  have h : (thetaBelowCell11003113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003113 h
theorem e24KC2ThetaBelowLeaf11003120 :
    adaptiveCoverCheck 10 thetaBelowCell11003120 = true := by
  have h : (thetaBelowCell11003120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003120 h
theorem e24KC2ThetaBelowLeaf11003121 :
    adaptiveCoverCheck 10 thetaBelowCell11003121 = true := by
  have h : (thetaBelowCell11003121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003121 h
theorem e24KC2ThetaBelowLeaf11003122 :
    adaptiveCoverCheck 10 thetaBelowCell11003122 = true := by
  have h : (thetaBelowCell11003122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003122 h
theorem e24KC2ThetaBelowLeaf11003123 :
    adaptiveCoverCheck 10 thetaBelowCell11003123 = true := by
  have h : (thetaBelowCell11003123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003123 h
theorem e24KC2ThetaBelowLeaf11003130 :
    adaptiveCoverCheck 10 thetaBelowCell11003130 = true := by
  have h : (thetaBelowCell11003130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003130 h
theorem e24KC2ThetaBelowLeaf11003131 :
    adaptiveCoverCheck 10 thetaBelowCell11003131 = true := by
  have h : (thetaBelowCell11003131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003131 h
theorem e24KC2ThetaBelowLeaf11003132 :
    adaptiveCoverCheck 10 thetaBelowCell11003132 = true := by
  have h : (thetaBelowCell11003132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003132 h
theorem e24KC2ThetaBelowLeaf11003133 :
    adaptiveCoverCheck 10 thetaBelowCell11003133 = true := by
  have h : (thetaBelowCell11003133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003133 h
theorem e24KC2ThetaBelowLeaf1100320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1100))) = true := by
  have h : ((childLL (childHL (childHH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1100))) = true := by
  have h : ((childLH (childHL (childHH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1100))) = true := by
  have h : ((childHL (childHL (childHH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1100))) = true := by
  have h : ((childHH (childHL (childHH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf11003300 :
    adaptiveCoverCheck 10 thetaBelowCell11003300 = true := by
  have h : (thetaBelowCell11003300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003300 h
theorem e24KC2ThetaBelowLeaf11003301 :
    adaptiveCoverCheck 10 thetaBelowCell11003301 = true := by
  have h : (thetaBelowCell11003301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003301 h
theorem e24KC2ThetaBelowLeaf11003302 :
    adaptiveCoverCheck 10 thetaBelowCell11003302 = true := by
  have h : (thetaBelowCell11003302).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003302 h
theorem e24KC2ThetaBelowLeaf11003303 :
    adaptiveCoverCheck 10 thetaBelowCell11003303 = true := by
  have h : (thetaBelowCell11003303).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003303 h
theorem e24KC2ThetaBelowLeaf11003310 :
    adaptiveCoverCheck 10 thetaBelowCell11003310 = true := by
  have h : (thetaBelowCell11003310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003310 h
theorem e24KC2ThetaBelowLeaf11003311 :
    adaptiveCoverCheck 10 thetaBelowCell11003311 = true := by
  have h : (thetaBelowCell11003311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003311 h
theorem e24KC2ThetaBelowLeaf11003312 :
    adaptiveCoverCheck 10 thetaBelowCell11003312 = true := by
  have h : (thetaBelowCell11003312).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003312 h
theorem e24KC2ThetaBelowLeaf11003313 :
    adaptiveCoverCheck 10 thetaBelowCell11003313 = true := by
  have h : (thetaBelowCell11003313).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11003313 h
theorem e24KC2ThetaBelowLeaf1100332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1100))) = true := by
  have h : ((childHL (childHH (childHH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf1100333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1100))) = true := by
  have h : ((childHH (childHH (childHH thetaBelowCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH thetaBelowCell1100))) h
theorem e24KC2ThetaBelowLeaf110100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1101)) = true := by
  have h : ((childLL (childLL thetaBelowCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1101)) h
theorem e24KC2ThetaBelowLeaf110101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1101)) = true := by
  have h : ((childLH (childLL thetaBelowCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1101)) h
theorem e24KC2ThetaBelowLeaf1101020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1101))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1101))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf11010220 :
    adaptiveCoverCheck 10 thetaBelowCell11010220 = true := by
  have h : (thetaBelowCell11010220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11010220 h
theorem e24KC2ThetaBelowLeaf11010221 :
    adaptiveCoverCheck 10 thetaBelowCell11010221 = true := by
  have h : (thetaBelowCell11010221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11010221 h
theorem e24KC2ThetaBelowLeaf11010222 :
    adaptiveCoverCheck 10 thetaBelowCell11010222 = true := by
  have h : (thetaBelowCell11010222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11010222 h
theorem e24KC2ThetaBelowLeaf11010223 :
    adaptiveCoverCheck 10 thetaBelowCell11010223 = true := by
  have h : (thetaBelowCell11010223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11010223 h
theorem e24KC2ThetaBelowLeaf11010230 :
    adaptiveCoverCheck 10 thetaBelowCell11010230 = true := by
  have h : (thetaBelowCell11010230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11010230 h
theorem e24KC2ThetaBelowLeaf11010231 :
    adaptiveCoverCheck 10 thetaBelowCell11010231 = true := by
  have h : (thetaBelowCell11010231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11010231 h
theorem e24KC2ThetaBelowLeaf11010232 :
    adaptiveCoverCheck 10 thetaBelowCell11010232 = true := by
  have h : (thetaBelowCell11010232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11010232 h
theorem e24KC2ThetaBelowLeaf11010233 :
    adaptiveCoverCheck 10 thetaBelowCell11010233 = true := by
  have h : (thetaBelowCell11010233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11010233 h
theorem e24KC2ThetaBelowLeaf1101030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1101))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1101))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1101))) = true := by
  have h : ((childHL (childHH (childLL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1101))) = true := by
  have h : ((childHH (childHH (childLL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf110110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1101)) = true := by
  have h : ((childLL (childLH thetaBelowCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1101)) h
theorem e24KC2ThetaBelowLeaf110111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1101)) = true := by
  have h : ((childLH (childLH thetaBelowCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1101)) h
theorem e24KC2ThetaBelowLeaf1101120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1101))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1101))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1101))) = true := by
  have h : ((childHL (childHL (childLH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1101))) = true := by
  have h : ((childHH (childHL (childLH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1101))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1101))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1101))) = true := by
  have h : ((childHL (childHH (childLH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1101))) = true := by
  have h : ((childHH (childHH (childLH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf11012000 :
    adaptiveCoverCheck 10 thetaBelowCell11012000 = true := by
  have h : (thetaBelowCell11012000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012000 h
theorem e24KC2ThetaBelowLeaf11012001 :
    adaptiveCoverCheck 10 thetaBelowCell11012001 = true := by
  have h : (thetaBelowCell11012001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012001 h
theorem e24KC2ThetaBelowLeaf11012002 :
    adaptiveCoverCheck 10 thetaBelowCell11012002 = true := by
  have h : (thetaBelowCell11012002).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012002 h
theorem e24KC2ThetaBelowLeaf11012003 :
    adaptiveCoverCheck 10 thetaBelowCell11012003 = true := by
  have h : (thetaBelowCell11012003).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012003 h
theorem e24KC2ThetaBelowLeaf11012010 :
    adaptiveCoverCheck 10 thetaBelowCell11012010 = true := by
  have h : (thetaBelowCell11012010).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012010 h
theorem e24KC2ThetaBelowLeaf11012011 :
    adaptiveCoverCheck 10 thetaBelowCell11012011 = true := by
  have h : (thetaBelowCell11012011).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012011 h
theorem e24KC2ThetaBelowLeaf11012012 :
    adaptiveCoverCheck 10 thetaBelowCell11012012 = true := by
  have h : (thetaBelowCell11012012).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012012 h
theorem e24KC2ThetaBelowLeaf11012013 :
    adaptiveCoverCheck 10 thetaBelowCell11012013 = true := by
  have h : (thetaBelowCell11012013).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012013 h
theorem e24KC2ThetaBelowLeaf11012020 :
    adaptiveCoverCheck 10 thetaBelowCell11012020 = true := by
  have h : (thetaBelowCell11012020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012020 h
theorem e24KC2ThetaBelowLeaf11012021 :
    adaptiveCoverCheck 10 thetaBelowCell11012021 = true := by
  have h : (thetaBelowCell11012021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012021 h
theorem e24KC2ThetaBelowLeaf11012022 :
    adaptiveCoverCheck 10 thetaBelowCell11012022 = true := by
  have h : (thetaBelowCell11012022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012022 h
theorem e24KC2ThetaBelowLeaf11012023 :
    adaptiveCoverCheck 10 thetaBelowCell11012023 = true := by
  have h : (thetaBelowCell11012023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012023 h
theorem e24KC2ThetaBelowLeaf11012030 :
    adaptiveCoverCheck 10 thetaBelowCell11012030 = true := by
  have h : (thetaBelowCell11012030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012030 h
theorem e24KC2ThetaBelowLeaf11012031 :
    adaptiveCoverCheck 10 thetaBelowCell11012031 = true := by
  have h : (thetaBelowCell11012031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012031 h
theorem e24KC2ThetaBelowLeaf11012032 :
    adaptiveCoverCheck 10 thetaBelowCell11012032 = true := by
  have h : (thetaBelowCell11012032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012032 h
theorem e24KC2ThetaBelowLeaf11012033 :
    adaptiveCoverCheck 10 thetaBelowCell11012033 = true := by
  have h : (thetaBelowCell11012033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012033 h
theorem e24KC2ThetaBelowLeaf11012100 :
    adaptiveCoverCheck 10 thetaBelowCell11012100 = true := by
  have h : (thetaBelowCell11012100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012100 h
theorem e24KC2ThetaBelowLeaf11012101 :
    adaptiveCoverCheck 10 thetaBelowCell11012101 = true := by
  have h : (thetaBelowCell11012101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012101 h
theorem e24KC2ThetaBelowLeaf11012102 :
    adaptiveCoverCheck 10 thetaBelowCell11012102 = true := by
  have h : (thetaBelowCell11012102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012102 h
theorem e24KC2ThetaBelowLeaf11012103 :
    adaptiveCoverCheck 10 thetaBelowCell11012103 = true := by
  have h : (thetaBelowCell11012103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012103 h
theorem e24KC2ThetaBelowLeaf11012110 :
    adaptiveCoverCheck 10 thetaBelowCell11012110 = true := by
  have h : (thetaBelowCell11012110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012110 h
theorem e24KC2ThetaBelowLeaf11012111 :
    adaptiveCoverCheck 10 thetaBelowCell11012111 = true := by
  have h : (thetaBelowCell11012111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012111 h
theorem e24KC2ThetaBelowLeaf11012112 :
    adaptiveCoverCheck 10 thetaBelowCell11012112 = true := by
  have h : (thetaBelowCell11012112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012112 h
theorem e24KC2ThetaBelowLeaf11012113 :
    adaptiveCoverCheck 10 thetaBelowCell11012113 = true := by
  have h : (thetaBelowCell11012113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012113 h
theorem e24KC2ThetaBelowLeaf11012120 :
    adaptiveCoverCheck 10 thetaBelowCell11012120 = true := by
  have h : (thetaBelowCell11012120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012120 h
theorem e24KC2ThetaBelowLeaf11012121 :
    adaptiveCoverCheck 10 thetaBelowCell11012121 = true := by
  have h : (thetaBelowCell11012121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012121 h
theorem e24KC2ThetaBelowLeaf11012122 :
    adaptiveCoverCheck 10 thetaBelowCell11012122 = true := by
  have h : (thetaBelowCell11012122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012122 h
theorem e24KC2ThetaBelowLeaf11012123 :
    adaptiveCoverCheck 10 thetaBelowCell11012123 = true := by
  have h : (thetaBelowCell11012123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012123 h
theorem e24KC2ThetaBelowLeaf11012130 :
    adaptiveCoverCheck 10 thetaBelowCell11012130 = true := by
  have h : (thetaBelowCell11012130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012130 h
theorem e24KC2ThetaBelowLeaf11012131 :
    adaptiveCoverCheck 10 thetaBelowCell11012131 = true := by
  have h : (thetaBelowCell11012131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012131 h
theorem e24KC2ThetaBelowLeaf110121320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11012132) = true := by
  have h : ((childLL thetaBelowCell11012132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11012132) h
theorem e24KC2ThetaBelowLeaf110121321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11012132) = true := by
  have h : ((childLH thetaBelowCell11012132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11012132) h
theorem e24KC2ThetaBelowLeaf110121322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11012132) = true := by
  have h : ((childHL thetaBelowCell11012132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11012132) h
theorem e24KC2ThetaBelowLeaf110121323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11012132) = true := by
  have h : ((childHH thetaBelowCell11012132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11012132) h
theorem e24KC2ThetaBelowLeaf110121330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11012133) = true := by
  have h : ((childLL thetaBelowCell11012133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11012133) h
theorem e24KC2ThetaBelowLeaf110121331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11012133) = true := by
  have h : ((childLH thetaBelowCell11012133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11012133) h
theorem e24KC2ThetaBelowLeaf110121332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11012133) = true := by
  have h : ((childHL thetaBelowCell11012133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11012133) h
theorem e24KC2ThetaBelowLeaf110121333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11012133) = true := by
  have h : ((childHH thetaBelowCell11012133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11012133) h
theorem e24KC2ThetaBelowLeaf11012200 :
    adaptiveCoverCheck 10 thetaBelowCell11012200 = true := by
  have h : (thetaBelowCell11012200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012200 h
theorem e24KC2ThetaBelowLeaf11012201 :
    adaptiveCoverCheck 10 thetaBelowCell11012201 = true := by
  have h : (thetaBelowCell11012201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012201 h
theorem e24KC2ThetaBelowLeaf11012202 :
    adaptiveCoverCheck 10 thetaBelowCell11012202 = true := by
  have h : (thetaBelowCell11012202).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012202 h
theorem e24KC2ThetaBelowLeaf11012203 :
    adaptiveCoverCheck 10 thetaBelowCell11012203 = true := by
  have h : (thetaBelowCell11012203).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012203 h
theorem e24KC2ThetaBelowLeaf11012210 :
    adaptiveCoverCheck 10 thetaBelowCell11012210 = true := by
  have h : (thetaBelowCell11012210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012210 h
theorem e24KC2ThetaBelowLeaf11012211 :
    adaptiveCoverCheck 10 thetaBelowCell11012211 = true := by
  have h : (thetaBelowCell11012211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012211 h
theorem e24KC2ThetaBelowLeaf11012212 :
    adaptiveCoverCheck 10 thetaBelowCell11012212 = true := by
  have h : (thetaBelowCell11012212).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012212 h
theorem e24KC2ThetaBelowLeaf11012213 :
    adaptiveCoverCheck 10 thetaBelowCell11012213 = true := by
  have h : (thetaBelowCell11012213).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012213 h
theorem e24KC2ThetaBelowLeaf1101222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL thetaBelowCell1101))) = true := by
  have h : ((childHL (childHL (childHL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL thetaBelowCell1101))) = true := by
  have h : ((childHH (childHL (childHL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf11012300 :
    adaptiveCoverCheck 10 thetaBelowCell11012300 = true := by
  have h : (thetaBelowCell11012300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012300 h
theorem e24KC2ThetaBelowLeaf11012301 :
    adaptiveCoverCheck 10 thetaBelowCell11012301 = true := by
  have h : (thetaBelowCell11012301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012301 h
theorem e24KC2ThetaBelowLeaf11012302 :
    adaptiveCoverCheck 10 thetaBelowCell11012302 = true := by
  have h : (thetaBelowCell11012302).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012302 h
theorem e24KC2ThetaBelowLeaf11012303 :
    adaptiveCoverCheck 10 thetaBelowCell11012303 = true := by
  have h : (thetaBelowCell11012303).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012303 h
theorem e24KC2ThetaBelowLeaf11012310 :
    adaptiveCoverCheck 10 thetaBelowCell11012310 = true := by
  have h : (thetaBelowCell11012310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012310 h
theorem e24KC2ThetaBelowLeaf11012311 :
    adaptiveCoverCheck 10 thetaBelowCell11012311 = true := by
  have h : (thetaBelowCell11012311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012311 h
theorem e24KC2ThetaBelowLeaf11012312 :
    adaptiveCoverCheck 10 thetaBelowCell11012312 = true := by
  have h : (thetaBelowCell11012312).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012312 h
theorem e24KC2ThetaBelowLeaf11012313 :
    adaptiveCoverCheck 10 thetaBelowCell11012313 = true := by
  have h : (thetaBelowCell11012313).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11012313 h
theorem e24KC2ThetaBelowLeaf1101232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL thetaBelowCell1101))) = true := by
  have h : ((childHL (childHH (childHL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL thetaBelowCell1101))) = true := by
  have h : ((childHH (childHH (childHL thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf11013000 :
    adaptiveCoverCheck 10 thetaBelowCell11013000 = true := by
  have h : (thetaBelowCell11013000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013000 h
theorem e24KC2ThetaBelowLeaf11013001 :
    adaptiveCoverCheck 10 thetaBelowCell11013001 = true := by
  have h : (thetaBelowCell11013001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013001 h
theorem e24KC2ThetaBelowLeaf11013002 :
    adaptiveCoverCheck 10 thetaBelowCell11013002 = true := by
  have h : (thetaBelowCell11013002).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013002 h
theorem e24KC2ThetaBelowLeaf11013003 :
    adaptiveCoverCheck 10 thetaBelowCell11013003 = true := by
  have h : (thetaBelowCell11013003).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013003 h
theorem e24KC2ThetaBelowLeaf11013010 :
    adaptiveCoverCheck 10 thetaBelowCell11013010 = true := by
  have h : (thetaBelowCell11013010).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013010 h
theorem e24KC2ThetaBelowLeaf11013011 :
    adaptiveCoverCheck 10 thetaBelowCell11013011 = true := by
  have h : (thetaBelowCell11013011).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013011 h
theorem e24KC2ThetaBelowLeaf11013012 :
    adaptiveCoverCheck 10 thetaBelowCell11013012 = true := by
  have h : (thetaBelowCell11013012).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013012 h
theorem e24KC2ThetaBelowLeaf110130130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013013) = true := by
  have h : ((childLL thetaBelowCell11013013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013013) h
theorem e24KC2ThetaBelowLeaf110130131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013013) = true := by
  have h : ((childLH thetaBelowCell11013013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013013) h
theorem e24KC2ThetaBelowLeaf110130132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013013) = true := by
  have h : ((childHL thetaBelowCell11013013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013013) h
theorem e24KC2ThetaBelowLeaf110130133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013013) = true := by
  have h : ((childHH thetaBelowCell11013013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013013) h
theorem e24KC2ThetaBelowLeaf11013020 :
    adaptiveCoverCheck 10 thetaBelowCell11013020 = true := by
  have h : (thetaBelowCell11013020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013020 h
theorem e24KC2ThetaBelowLeaf110130210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013021) = true := by
  have h : ((childLL thetaBelowCell11013021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013021) h
theorem e24KC2ThetaBelowLeaf110130211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013021) = true := by
  have h : ((childLH thetaBelowCell11013021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013021) h
theorem e24KC2ThetaBelowLeaf110130212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013021) = true := by
  have h : ((childHL thetaBelowCell11013021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013021) h
theorem e24KC2ThetaBelowLeaf110130213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013021) = true := by
  have h : ((childHH thetaBelowCell11013021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013021) h
theorem e24KC2ThetaBelowLeaf110130220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013022) = true := by
  have h : ((childLL thetaBelowCell11013022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013022) h
theorem e24KC2ThetaBelowLeaf110130221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013022) = true := by
  have h : ((childLH thetaBelowCell11013022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013022) h
theorem e24KC2ThetaBelowLeaf110130222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013022) = true := by
  have h : ((childHL thetaBelowCell11013022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013022) h
theorem e24KC2ThetaBelowLeaf110130223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013022) = true := by
  have h : ((childHH thetaBelowCell11013022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013022) h
theorem e24KC2ThetaBelowLeaf110130230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013023) = true := by
  have h : ((childLL thetaBelowCell11013023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013023) h
theorem e24KC2ThetaBelowLeaf110130231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013023) = true := by
  have h : ((childLH thetaBelowCell11013023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013023) h
theorem e24KC2ThetaBelowLeaf110130232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013023) = true := by
  have h : ((childHL thetaBelowCell11013023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013023) h
theorem e24KC2ThetaBelowLeaf110130233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013023) = true := by
  have h : ((childHH thetaBelowCell11013023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013023) h
theorem e24KC2ThetaBelowLeaf110130300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013030) = true := by
  have h : ((childLL thetaBelowCell11013030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013030) h
theorem e24KC2ThetaBelowLeaf110130301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013030) = true := by
  have h : ((childLH thetaBelowCell11013030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013030) h
theorem e24KC2ThetaBelowLeaf110130302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013030) = true := by
  have h : ((childHL thetaBelowCell11013030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013030) h
theorem e24KC2ThetaBelowLeaf110130303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013030) = true := by
  have h : ((childHH thetaBelowCell11013030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013030) h
theorem e24KC2ThetaBelowLeaf110130310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013031) = true := by
  have h : ((childLL thetaBelowCell11013031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013031) h
theorem e24KC2ThetaBelowLeaf110130311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013031) = true := by
  have h : ((childLH thetaBelowCell11013031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013031) h
theorem e24KC2ThetaBelowLeaf110130312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013031) = true := by
  have h : ((childHL thetaBelowCell11013031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013031) h
theorem e24KC2ThetaBelowLeaf110130313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013031) = true := by
  have h : ((childHH thetaBelowCell11013031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013031) h
theorem e24KC2ThetaBelowLeaf110130320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013032) = true := by
  have h : ((childLL thetaBelowCell11013032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013032) h
theorem e24KC2ThetaBelowLeaf110130321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013032) = true := by
  have h : ((childLH thetaBelowCell11013032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013032) h
theorem e24KC2ThetaBelowLeaf110130322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013032) = true := by
  have h : ((childHL thetaBelowCell11013032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013032) h
theorem e24KC2ThetaBelowLeaf110130323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013032) = true := by
  have h : ((childHH thetaBelowCell11013032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013032) h
theorem e24KC2ThetaBelowLeaf110130330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013033) = true := by
  have h : ((childLL thetaBelowCell11013033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013033) h
theorem e24KC2ThetaBelowLeaf110130331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013033) = true := by
  have h : ((childLH thetaBelowCell11013033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013033) h
theorem e24KC2ThetaBelowLeaf110130332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013033) = true := by
  have h : ((childHL thetaBelowCell11013033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013033) h
theorem e24KC2ThetaBelowLeaf110130333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013033) = true := by
  have h : ((childHH thetaBelowCell11013033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013033) h
theorem e24KC2ThetaBelowLeaf11013100 :
    adaptiveCoverCheck 10 thetaBelowCell11013100 = true := by
  have h : (thetaBelowCell11013100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013100 h
theorem e24KC2ThetaBelowLeaf11013101 :
    adaptiveCoverCheck 10 thetaBelowCell11013101 = true := by
  have h : (thetaBelowCell11013101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013101 h
theorem e24KC2ThetaBelowLeaf110131020 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013102) = true := by
  have h : ((childLL thetaBelowCell11013102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013102) h
theorem e24KC2ThetaBelowLeaf110131021 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013102) = true := by
  have h : ((childLH thetaBelowCell11013102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013102) h
theorem e24KC2ThetaBelowLeaf110131022 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013102) = true := by
  have h : ((childHL thetaBelowCell11013102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013102) h
theorem e24KC2ThetaBelowLeaf110131023 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013102) = true := by
  have h : ((childHH thetaBelowCell11013102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013102) h
theorem e24KC2ThetaBelowLeaf110131030 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013103) = true := by
  have h : ((childLL thetaBelowCell11013103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013103) h
theorem e24KC2ThetaBelowLeaf110131031 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013103) = true := by
  have h : ((childLH thetaBelowCell11013103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013103) h
theorem e24KC2ThetaBelowLeaf110131032 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013103) = true := by
  have h : ((childHL thetaBelowCell11013103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013103) h
theorem e24KC2ThetaBelowLeaf110131033 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013103) = true := by
  have h : ((childHH thetaBelowCell11013103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013103) h
theorem e24KC2ThetaBelowLeaf11013110 :
    adaptiveCoverCheck 10 thetaBelowCell11013110 = true := by
  have h : (thetaBelowCell11013110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013110 h
theorem e24KC2ThetaBelowLeaf11013111 :
    adaptiveCoverCheck 10 thetaBelowCell11013111 = true := by
  have h : (thetaBelowCell11013111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013111 h
theorem e24KC2ThetaBelowLeaf110131120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013112) = true := by
  have h : ((childLL thetaBelowCell11013112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013112) h
theorem e24KC2ThetaBelowLeaf110131121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013112) = true := by
  have h : ((childLH thetaBelowCell11013112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013112) h
theorem e24KC2ThetaBelowLeaf110131122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013112) = true := by
  have h : ((childHL thetaBelowCell11013112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013112) h
theorem e24KC2ThetaBelowLeaf110131123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013112) = true := by
  have h : ((childHH thetaBelowCell11013112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013112) h
theorem e24KC2ThetaBelowLeaf110131130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013113) = true := by
  have h : ((childLL thetaBelowCell11013113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013113) h
theorem e24KC2ThetaBelowLeaf110131131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013113) = true := by
  have h : ((childLH thetaBelowCell11013113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013113) h
theorem e24KC2ThetaBelowLeaf110131132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013113) = true := by
  have h : ((childHL thetaBelowCell11013113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013113) h
theorem e24KC2ThetaBelowLeaf110131133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013113) = true := by
  have h : ((childHH thetaBelowCell11013113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013113) h
theorem e24KC2ThetaBelowLeaf110131200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013120) = true := by
  have h : ((childLL thetaBelowCell11013120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013120) h
theorem e24KC2ThetaBelowLeaf110131201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013120) = true := by
  have h : ((childLH thetaBelowCell11013120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013120) h
theorem e24KC2ThetaBelowLeaf110131202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013120) = true := by
  have h : ((childHL thetaBelowCell11013120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013120) h
theorem e24KC2ThetaBelowLeaf110131203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013120) = true := by
  have h : ((childHH thetaBelowCell11013120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013120) h
theorem e24KC2ThetaBelowLeaf110131210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013121) = true := by
  have h : ((childLL thetaBelowCell11013121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013121) h
theorem e24KC2ThetaBelowLeaf110131211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013121) = true := by
  have h : ((childLH thetaBelowCell11013121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013121) h
theorem e24KC2ThetaBelowLeaf110131212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013121) = true := by
  have h : ((childHL thetaBelowCell11013121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013121) h
theorem e24KC2ThetaBelowLeaf110131213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013121) = true := by
  have h : ((childHH thetaBelowCell11013121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013121) h
theorem e24KC2ThetaBelowLeaf110131220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013122) = true := by
  have h : ((childLL thetaBelowCell11013122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013122) h
theorem e24KC2ThetaBelowLeaf110131221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013122) = true := by
  have h : ((childLH thetaBelowCell11013122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013122) h
theorem e24KC2ThetaBelowLeaf110131222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013122) = true := by
  have h : ((childHL thetaBelowCell11013122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013122) h
theorem e24KC2ThetaBelowLeaf110131223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013122) = true := by
  have h : ((childHH thetaBelowCell11013122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013122) h
theorem e24KC2ThetaBelowLeaf110131230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013123) = true := by
  have h : ((childLL thetaBelowCell11013123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013123) h
theorem e24KC2ThetaBelowLeaf110131231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013123) = true := by
  have h : ((childLH thetaBelowCell11013123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013123) h
theorem e24KC2ThetaBelowLeaf110131232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013123) = true := by
  have h : ((childHL thetaBelowCell11013123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013123) h
theorem e24KC2ThetaBelowLeaf110131233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013123) = true := by
  have h : ((childHH thetaBelowCell11013123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013123) h
theorem e24KC2ThetaBelowLeaf110131300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013130) = true := by
  have h : ((childLL thetaBelowCell11013130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013130) h
theorem e24KC2ThetaBelowLeaf110131301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013130) = true := by
  have h : ((childLH thetaBelowCell11013130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013130) h
theorem e24KC2ThetaBelowLeaf110131302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013130) = true := by
  have h : ((childHL thetaBelowCell11013130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013130) h
theorem e24KC2ThetaBelowLeaf110131303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013130) = true := by
  have h : ((childHH thetaBelowCell11013130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013130) h
theorem e24KC2ThetaBelowLeaf110131310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013131) = true := by
  have h : ((childLL thetaBelowCell11013131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013131) h
theorem e24KC2ThetaBelowLeaf110131311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013131) = true := by
  have h : ((childLH thetaBelowCell11013131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013131) h
theorem e24KC2ThetaBelowLeaf110131312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013131) = true := by
  have h : ((childHL thetaBelowCell11013131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013131) h
theorem e24KC2ThetaBelowLeaf110131313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013131) = true := by
  have h : ((childHH thetaBelowCell11013131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013131) h
theorem e24KC2ThetaBelowLeaf110131320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013132) = true := by
  have h : ((childLL thetaBelowCell11013132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013132) h
theorem e24KC2ThetaBelowLeaf110131321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013132) = true := by
  have h : ((childLH thetaBelowCell11013132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013132) h
theorem e24KC2ThetaBelowLeaf110131322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013132) = true := by
  have h : ((childHL thetaBelowCell11013132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013132) h
theorem e24KC2ThetaBelowLeaf110131323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013132) = true := by
  have h : ((childHH thetaBelowCell11013132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013132) h
theorem e24KC2ThetaBelowLeaf110131330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11013133) = true := by
  have h : ((childLL thetaBelowCell11013133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11013133) h
theorem e24KC2ThetaBelowLeaf110131331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11013133) = true := by
  have h : ((childLH thetaBelowCell11013133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11013133) h
theorem e24KC2ThetaBelowLeaf110131332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11013133) = true := by
  have h : ((childHL thetaBelowCell11013133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11013133) h
theorem e24KC2ThetaBelowLeaf110131333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11013133) = true := by
  have h : ((childHH thetaBelowCell11013133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11013133) h
theorem e24KC2ThetaBelowLeaf11013200 :
    adaptiveCoverCheck 10 thetaBelowCell11013200 = true := by
  have h : (thetaBelowCell11013200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013200 h
theorem e24KC2ThetaBelowLeaf11013201 :
    adaptiveCoverCheck 10 thetaBelowCell11013201 = true := by
  have h : (thetaBelowCell11013201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013201 h
theorem e24KC2ThetaBelowLeaf11013202 :
    adaptiveCoverCheck 10 thetaBelowCell11013202 = true := by
  have h : (thetaBelowCell11013202).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013202 h
theorem e24KC2ThetaBelowLeaf11013203 :
    adaptiveCoverCheck 10 thetaBelowCell11013203 = true := by
  have h : (thetaBelowCell11013203).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013203 h
theorem e24KC2ThetaBelowLeaf11013210 :
    adaptiveCoverCheck 10 thetaBelowCell11013210 = true := by
  have h : (thetaBelowCell11013210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013210 h
theorem e24KC2ThetaBelowLeaf11013211 :
    adaptiveCoverCheck 10 thetaBelowCell11013211 = true := by
  have h : (thetaBelowCell11013211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013211 h
theorem e24KC2ThetaBelowLeaf11013212 :
    adaptiveCoverCheck 10 thetaBelowCell11013212 = true := by
  have h : (thetaBelowCell11013212).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013212 h
theorem e24KC2ThetaBelowLeaf11013213 :
    adaptiveCoverCheck 10 thetaBelowCell11013213 = true := by
  have h : (thetaBelowCell11013213).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013213 h
theorem e24KC2ThetaBelowLeaf1101322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1101))) = true := by
  have h : ((childHL (childHL (childHH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1101))) = true := by
  have h : ((childHH (childHL (childHH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf11013300 :
    adaptiveCoverCheck 10 thetaBelowCell11013300 = true := by
  have h : (thetaBelowCell11013300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013300 h
theorem e24KC2ThetaBelowLeaf11013301 :
    adaptiveCoverCheck 10 thetaBelowCell11013301 = true := by
  have h : (thetaBelowCell11013301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013301 h
theorem e24KC2ThetaBelowLeaf11013302 :
    adaptiveCoverCheck 10 thetaBelowCell11013302 = true := by
  have h : (thetaBelowCell11013302).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013302 h
theorem e24KC2ThetaBelowLeaf11013303 :
    adaptiveCoverCheck 10 thetaBelowCell11013303 = true := by
  have h : (thetaBelowCell11013303).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013303 h
theorem e24KC2ThetaBelowLeaf11013310 :
    adaptiveCoverCheck 10 thetaBelowCell11013310 = true := by
  have h : (thetaBelowCell11013310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013310 h
theorem e24KC2ThetaBelowLeaf11013311 :
    adaptiveCoverCheck 10 thetaBelowCell11013311 = true := by
  have h : (thetaBelowCell11013311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013311 h
theorem e24KC2ThetaBelowLeaf11013312 :
    adaptiveCoverCheck 10 thetaBelowCell11013312 = true := by
  have h : (thetaBelowCell11013312).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013312 h
theorem e24KC2ThetaBelowLeaf11013313 :
    adaptiveCoverCheck 10 thetaBelowCell11013313 = true := by
  have h : (thetaBelowCell11013313).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11013313 h
theorem e24KC2ThetaBelowLeaf1101332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1101))) = true := by
  have h : ((childHL (childHH (childHH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf1101333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1101))) = true := by
  have h : ((childHH (childHH (childHH thetaBelowCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH thetaBelowCell1101))) h
theorem e24KC2ThetaBelowLeaf110200 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1102)) = true := by
  have h : ((childLL (childLL thetaBelowCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1102)) h
theorem e24KC2ThetaBelowLeaf110201 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1102)) = true := by
  have h : ((childLH (childLL thetaBelowCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1102)) h
theorem e24KC2ThetaBelowLeaf110202 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1102)) = true := by
  have h : ((childHL (childLL thetaBelowCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1102)) h
theorem e24KC2ThetaBelowLeaf110203 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1102)) = true := by
  have h : ((childHH (childLL thetaBelowCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1102)) h
theorem e24KC2ThetaBelowLeaf110210 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1102)) = true := by
  have h : ((childLL (childLH thetaBelowCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1102)) h
theorem e24KC2ThetaBelowLeaf110211 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1102)) = true := by
  have h : ((childLH (childLH thetaBelowCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1102)) h
theorem e24KC2ThetaBelowLeaf110212 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1102)) = true := by
  have h : ((childHL (childLH thetaBelowCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1102)) h
theorem e24KC2ThetaBelowLeaf110213 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1102)) = true := by
  have h : ((childHH (childLH thetaBelowCell1102))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1102)) h
theorem e24KC2ThetaBelowLeaf11022 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1102) = true := by
  have h : ((childHL thetaBelowCell1102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1102) h
theorem e24KC2ThetaBelowLeaf11023 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1102) = true := by
  have h : ((childHH thetaBelowCell1102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1102) h
theorem e24KC2ThetaBelowLeaf110300 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1103)) = true := by
  have h : ((childLL (childLL thetaBelowCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1103)) h
theorem e24KC2ThetaBelowLeaf110301 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1103)) = true := by
  have h : ((childLH (childLL thetaBelowCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1103)) h
theorem e24KC2ThetaBelowLeaf110302 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1103)) = true := by
  have h : ((childHL (childLL thetaBelowCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1103)) h
theorem e24KC2ThetaBelowLeaf110303 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1103)) = true := by
  have h : ((childHH (childLL thetaBelowCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1103)) h
theorem e24KC2ThetaBelowLeaf110310 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1103)) = true := by
  have h : ((childLL (childLH thetaBelowCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1103)) h
theorem e24KC2ThetaBelowLeaf110311 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1103)) = true := by
  have h : ((childLH (childLH thetaBelowCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1103)) h
theorem e24KC2ThetaBelowLeaf110312 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1103)) = true := by
  have h : ((childHL (childLH thetaBelowCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1103)) h
theorem e24KC2ThetaBelowLeaf110313 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1103)) = true := by
  have h : ((childHH (childLH thetaBelowCell1103))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1103)) h
theorem e24KC2ThetaBelowLeaf11032 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1103) = true := by
  have h : ((childHL thetaBelowCell1103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1103) h
theorem e24KC2ThetaBelowLeaf11033 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1103) = true := by
  have h : ((childHH thetaBelowCell1103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1103) h
theorem e24KC2ThetaBelowLeaf111000 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1110)) = true := by
  have h : ((childLL (childLL thetaBelowCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1110)) h
theorem e24KC2ThetaBelowLeaf111001 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1110)) = true := by
  have h : ((childLH (childLL thetaBelowCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1110)) h
theorem e24KC2ThetaBelowLeaf1110020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1110))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1110))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1110))) = true := by
  have h : ((childHL (childHL (childLL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1110))) = true := by
  have h : ((childHH (childHL (childLL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1110))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1110))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1110))) = true := by
  have h : ((childHL (childHH (childLL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1110))) = true := by
  have h : ((childHH (childHH (childLL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf111010 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1110)) = true := by
  have h : ((childLL (childLH thetaBelowCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1110)) h
theorem e24KC2ThetaBelowLeaf111011 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1110)) = true := by
  have h : ((childLH (childLH thetaBelowCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1110)) h
theorem e24KC2ThetaBelowLeaf1110120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1110))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1110))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1110))) = true := by
  have h : ((childHL (childHL (childLH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1110))) = true := by
  have h : ((childHH (childHL (childLH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1110))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1110))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1110))) = true := by
  have h : ((childHL (childHH (childLH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1110))) = true := by
  have h : ((childHH (childHH (childLH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf11102000 :
    adaptiveCoverCheck 10 thetaBelowCell11102000 = true := by
  have h : (thetaBelowCell11102000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102000 h
theorem e24KC2ThetaBelowLeaf11102001 :
    adaptiveCoverCheck 10 thetaBelowCell11102001 = true := by
  have h : (thetaBelowCell11102001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102001 h
theorem e24KC2ThetaBelowLeaf111020020 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102002) = true := by
  have h : ((childLL thetaBelowCell11102002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102002) h
theorem e24KC2ThetaBelowLeaf111020021 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102002) = true := by
  have h : ((childLH thetaBelowCell11102002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102002) h
theorem e24KC2ThetaBelowLeaf111020022 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102002) = true := by
  have h : ((childHL thetaBelowCell11102002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102002) h
theorem e24KC2ThetaBelowLeaf111020023 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102002) = true := by
  have h : ((childHH thetaBelowCell11102002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102002) h
theorem e24KC2ThetaBelowLeaf111020030 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102003) = true := by
  have h : ((childLL thetaBelowCell11102003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102003) h
theorem e24KC2ThetaBelowLeaf111020031 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102003) = true := by
  have h : ((childLH thetaBelowCell11102003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102003) h
theorem e24KC2ThetaBelowLeaf111020032 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102003) = true := by
  have h : ((childHL thetaBelowCell11102003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102003) h
theorem e24KC2ThetaBelowLeaf111020033 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102003) = true := by
  have h : ((childHH thetaBelowCell11102003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102003) h
theorem e24KC2ThetaBelowLeaf11102010 :
    adaptiveCoverCheck 10 thetaBelowCell11102010 = true := by
  have h : (thetaBelowCell11102010).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102010 h
theorem e24KC2ThetaBelowLeaf11102011 :
    adaptiveCoverCheck 10 thetaBelowCell11102011 = true := by
  have h : (thetaBelowCell11102011).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102011 h
theorem e24KC2ThetaBelowLeaf111020120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102012) = true := by
  have h : ((childLL thetaBelowCell11102012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102012) h
theorem e24KC2ThetaBelowLeaf111020121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102012) = true := by
  have h : ((childLH thetaBelowCell11102012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102012) h
theorem e24KC2ThetaBelowLeaf111020122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102012) = true := by
  have h : ((childHL thetaBelowCell11102012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102012) h
theorem e24KC2ThetaBelowLeaf111020123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102012) = true := by
  have h : ((childHH thetaBelowCell11102012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102012) h
theorem e24KC2ThetaBelowLeaf111020130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102013) = true := by
  have h : ((childLL thetaBelowCell11102013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102013) h
theorem e24KC2ThetaBelowLeaf111020131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102013) = true := by
  have h : ((childLH thetaBelowCell11102013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102013) h
theorem e24KC2ThetaBelowLeaf111020132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102013) = true := by
  have h : ((childHL thetaBelowCell11102013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102013) h
theorem e24KC2ThetaBelowLeaf111020133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102013) = true := by
  have h : ((childHH thetaBelowCell11102013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102013) h
theorem e24KC2ThetaBelowLeaf111020200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102020) = true := by
  have h : ((childLL thetaBelowCell11102020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102020) h
theorem e24KC2ThetaBelowLeaf111020201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102020) = true := by
  have h : ((childLH thetaBelowCell11102020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102020) h
theorem e24KC2ThetaBelowLeaf111020202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102020) = true := by
  have h : ((childHL thetaBelowCell11102020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102020) h
theorem e24KC2ThetaBelowLeaf111020203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102020) = true := by
  have h : ((childHH thetaBelowCell11102020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102020) h
theorem e24KC2ThetaBelowLeaf111020210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102021) = true := by
  have h : ((childLL thetaBelowCell11102021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102021) h
theorem e24KC2ThetaBelowLeaf111020211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102021) = true := by
  have h : ((childLH thetaBelowCell11102021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102021) h
theorem e24KC2ThetaBelowLeaf111020212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102021) = true := by
  have h : ((childHL thetaBelowCell11102021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102021) h
theorem e24KC2ThetaBelowLeaf111020213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102021) = true := by
  have h : ((childHH thetaBelowCell11102021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102021) h
theorem e24KC2ThetaBelowLeaf111020220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102022) = true := by
  have h : ((childLL thetaBelowCell11102022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102022) h
theorem e24KC2ThetaBelowLeaf111020221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102022) = true := by
  have h : ((childLH thetaBelowCell11102022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102022) h
theorem e24KC2ThetaBelowLeaf111020222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102022) = true := by
  have h : ((childHL thetaBelowCell11102022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102022) h
theorem e24KC2ThetaBelowLeaf111020223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102022) = true := by
  have h : ((childHH thetaBelowCell11102022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102022) h
theorem e24KC2ThetaBelowLeaf111020230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102023) = true := by
  have h : ((childLL thetaBelowCell11102023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102023) h
theorem e24KC2ThetaBelowLeaf111020231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102023) = true := by
  have h : ((childLH thetaBelowCell11102023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102023) h
theorem e24KC2ThetaBelowLeaf111020232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102023) = true := by
  have h : ((childHL thetaBelowCell11102023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102023) h
theorem e24KC2ThetaBelowLeaf111020233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102023) = true := by
  have h : ((childHH thetaBelowCell11102023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102023) h
theorem e24KC2ThetaBelowLeaf111020300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102030) = true := by
  have h : ((childLL thetaBelowCell11102030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102030) h
theorem e24KC2ThetaBelowLeaf111020301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102030) = true := by
  have h : ((childLH thetaBelowCell11102030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102030) h
theorem e24KC2ThetaBelowLeaf111020302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102030) = true := by
  have h : ((childHL thetaBelowCell11102030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102030) h
theorem e24KC2ThetaBelowLeaf111020303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102030) = true := by
  have h : ((childHH thetaBelowCell11102030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102030) h
theorem e24KC2ThetaBelowLeaf111020310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102031) = true := by
  have h : ((childLL thetaBelowCell11102031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102031) h
theorem e24KC2ThetaBelowLeaf111020311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102031) = true := by
  have h : ((childLH thetaBelowCell11102031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102031) h
theorem e24KC2ThetaBelowLeaf111020312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102031) = true := by
  have h : ((childHL thetaBelowCell11102031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102031) h
theorem e24KC2ThetaBelowLeaf111020313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102031) = true := by
  have h : ((childHH thetaBelowCell11102031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102031) h
theorem e24KC2ThetaBelowLeaf111020320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102032) = true := by
  have h : ((childLL thetaBelowCell11102032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102032) h
theorem e24KC2ThetaBelowLeaf111020321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102032) = true := by
  have h : ((childLH thetaBelowCell11102032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102032) h
theorem e24KC2ThetaBelowLeaf111020322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102032) = true := by
  have h : ((childHL thetaBelowCell11102032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102032) h
theorem e24KC2ThetaBelowLeaf111020323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102032) = true := by
  have h : ((childHH thetaBelowCell11102032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102032) h
theorem e24KC2ThetaBelowLeaf111020330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102033) = true := by
  have h : ((childLL thetaBelowCell11102033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102033) h
theorem e24KC2ThetaBelowLeaf111020331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102033) = true := by
  have h : ((childLH thetaBelowCell11102033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102033) h
theorem e24KC2ThetaBelowLeaf111020332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102033) = true := by
  have h : ((childHL thetaBelowCell11102033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102033) h
theorem e24KC2ThetaBelowLeaf111020333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102033) = true := by
  have h : ((childHH thetaBelowCell11102033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102033) h
theorem e24KC2ThetaBelowLeaf11102100 :
    adaptiveCoverCheck 10 thetaBelowCell11102100 = true := by
  have h : (thetaBelowCell11102100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102100 h
theorem e24KC2ThetaBelowLeaf11102101 :
    adaptiveCoverCheck 10 thetaBelowCell11102101 = true := by
  have h : (thetaBelowCell11102101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102101 h
theorem e24KC2ThetaBelowLeaf11102102 :
    adaptiveCoverCheck 10 thetaBelowCell11102102 = true := by
  have h : (thetaBelowCell11102102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102102 h
theorem e24KC2ThetaBelowLeaf11102103 :
    adaptiveCoverCheck 10 thetaBelowCell11102103 = true := by
  have h : (thetaBelowCell11102103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102103 h
theorem e24KC2ThetaBelowLeaf11102110 :
    adaptiveCoverCheck 10 thetaBelowCell11102110 = true := by
  have h : (thetaBelowCell11102110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102110 h
theorem e24KC2ThetaBelowLeaf11102111 :
    adaptiveCoverCheck 10 thetaBelowCell11102111 = true := by
  have h : (thetaBelowCell11102111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102111 h
theorem e24KC2ThetaBelowLeaf11102112 :
    adaptiveCoverCheck 10 thetaBelowCell11102112 = true := by
  have h : (thetaBelowCell11102112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102112 h
theorem e24KC2ThetaBelowLeaf11102113 :
    adaptiveCoverCheck 10 thetaBelowCell11102113 = true := by
  have h : (thetaBelowCell11102113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102113 h
theorem e24KC2ThetaBelowLeaf111021200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102120) = true := by
  have h : ((childLL thetaBelowCell11102120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102120) h
theorem e24KC2ThetaBelowLeaf111021201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102120) = true := by
  have h : ((childLH thetaBelowCell11102120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102120) h
theorem e24KC2ThetaBelowLeaf111021202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102120) = true := by
  have h : ((childHL thetaBelowCell11102120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102120) h
theorem e24KC2ThetaBelowLeaf111021203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102120) = true := by
  have h : ((childHH thetaBelowCell11102120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102120) h
theorem e24KC2ThetaBelowLeaf111021210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102121) = true := by
  have h : ((childLL thetaBelowCell11102121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102121) h
theorem e24KC2ThetaBelowLeaf111021211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102121) = true := by
  have h : ((childLH thetaBelowCell11102121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102121) h
theorem e24KC2ThetaBelowLeaf111021212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102121) = true := by
  have h : ((childHL thetaBelowCell11102121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102121) h
theorem e24KC2ThetaBelowLeaf111021213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102121) = true := by
  have h : ((childHH thetaBelowCell11102121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102121) h
theorem e24KC2ThetaBelowLeaf111021220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102122) = true := by
  have h : ((childLL thetaBelowCell11102122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102122) h
theorem e24KC2ThetaBelowLeaf111021221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102122) = true := by
  have h : ((childLH thetaBelowCell11102122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102122) h
theorem e24KC2ThetaBelowLeaf111021222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102122) = true := by
  have h : ((childHL thetaBelowCell11102122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102122) h
theorem e24KC2ThetaBelowLeaf111021223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102122) = true := by
  have h : ((childHH thetaBelowCell11102122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102122) h
theorem e24KC2ThetaBelowLeaf111021230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102123) = true := by
  have h : ((childLL thetaBelowCell11102123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102123) h
theorem e24KC2ThetaBelowLeaf111021231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102123) = true := by
  have h : ((childLH thetaBelowCell11102123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102123) h
theorem e24KC2ThetaBelowLeaf111021232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102123) = true := by
  have h : ((childHL thetaBelowCell11102123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102123) h
theorem e24KC2ThetaBelowLeaf111021233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102123) = true := by
  have h : ((childHH thetaBelowCell11102123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102123) h
theorem e24KC2ThetaBelowLeaf111021300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102130) = true := by
  have h : ((childLL thetaBelowCell11102130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102130) h
theorem e24KC2ThetaBelowLeaf111021301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102130) = true := by
  have h : ((childLH thetaBelowCell11102130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102130) h
theorem e24KC2ThetaBelowLeaf111021302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102130) = true := by
  have h : ((childHL thetaBelowCell11102130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102130) h
theorem e24KC2ThetaBelowLeaf111021303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102130) = true := by
  have h : ((childHH thetaBelowCell11102130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102130) h
theorem e24KC2ThetaBelowLeaf111021310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102131) = true := by
  have h : ((childLL thetaBelowCell11102131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102131) h
theorem e24KC2ThetaBelowLeaf111021311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102131) = true := by
  have h : ((childLH thetaBelowCell11102131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102131) h
theorem e24KC2ThetaBelowLeaf111021312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102131) = true := by
  have h : ((childHL thetaBelowCell11102131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102131) h
theorem e24KC2ThetaBelowLeaf111021313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102131) = true := by
  have h : ((childHH thetaBelowCell11102131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102131) h
theorem e24KC2ThetaBelowLeaf111021320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102132) = true := by
  have h : ((childLL thetaBelowCell11102132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102132) h
theorem e24KC2ThetaBelowLeaf111021321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102132) = true := by
  have h : ((childLH thetaBelowCell11102132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102132) h
theorem e24KC2ThetaBelowLeaf111021322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102132) = true := by
  have h : ((childHL thetaBelowCell11102132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102132) h
theorem e24KC2ThetaBelowLeaf111021323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102132) = true := by
  have h : ((childHH thetaBelowCell11102132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102132) h
theorem e24KC2ThetaBelowLeaf111021330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102133) = true := by
  have h : ((childLL thetaBelowCell11102133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102133) h
theorem e24KC2ThetaBelowLeaf111021331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102133) = true := by
  have h : ((childLH thetaBelowCell11102133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102133) h
theorem e24KC2ThetaBelowLeaf111021332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102133) = true := by
  have h : ((childHL thetaBelowCell11102133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102133) h
theorem e24KC2ThetaBelowLeaf111021333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102133) = true := by
  have h : ((childHH thetaBelowCell11102133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102133) h
theorem e24KC2ThetaBelowLeaf111022000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102200) = true := by
  have h : ((childLL thetaBelowCell11102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102200) h
theorem e24KC2ThetaBelowLeaf111022001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102200) = true := by
  have h : ((childLH thetaBelowCell11102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102200) h
theorem e24KC2ThetaBelowLeaf111022002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102200) = true := by
  have h : ((childHL thetaBelowCell11102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102200) h
theorem e24KC2ThetaBelowLeaf111022003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102200) = true := by
  have h : ((childHH thetaBelowCell11102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102200) h
theorem e24KC2ThetaBelowLeaf111022010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102201) = true := by
  have h : ((childLL thetaBelowCell11102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102201) h
theorem e24KC2ThetaBelowLeaf111022011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102201) = true := by
  have h : ((childLH thetaBelowCell11102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102201) h
theorem e24KC2ThetaBelowLeaf111022012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102201) = true := by
  have h : ((childHL thetaBelowCell11102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102201) h
theorem e24KC2ThetaBelowLeaf111022013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102201) = true := by
  have h : ((childHH thetaBelowCell11102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102201) h
theorem e24KC2ThetaBelowLeaf11102202 :
    adaptiveCoverCheck 10 thetaBelowCell11102202 = true := by
  have h : (thetaBelowCell11102202).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102202 h
theorem e24KC2ThetaBelowLeaf11102203 :
    adaptiveCoverCheck 10 thetaBelowCell11102203 = true := by
  have h : (thetaBelowCell11102203).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102203 h
theorem e24KC2ThetaBelowLeaf111022100 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102210) = true := by
  have h : ((childLL thetaBelowCell11102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102210) h
theorem e24KC2ThetaBelowLeaf111022101 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102210) = true := by
  have h : ((childLH thetaBelowCell11102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102210) h
theorem e24KC2ThetaBelowLeaf111022102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102210) = true := by
  have h : ((childHL thetaBelowCell11102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102210) h
theorem e24KC2ThetaBelowLeaf111022103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102210) = true := by
  have h : ((childHH thetaBelowCell11102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102210) h
theorem e24KC2ThetaBelowLeaf111022110 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102211) = true := by
  have h : ((childLL thetaBelowCell11102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102211) h
theorem e24KC2ThetaBelowLeaf111022111 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102211) = true := by
  have h : ((childLH thetaBelowCell11102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102211) h
theorem e24KC2ThetaBelowLeaf111022112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102211) = true := by
  have h : ((childHL thetaBelowCell11102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102211) h
theorem e24KC2ThetaBelowLeaf111022113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102211) = true := by
  have h : ((childHH thetaBelowCell11102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102211) h
theorem e24KC2ThetaBelowLeaf11102212 :
    adaptiveCoverCheck 10 thetaBelowCell11102212 = true := by
  have h : (thetaBelowCell11102212).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102212 h
theorem e24KC2ThetaBelowLeaf11102213 :
    adaptiveCoverCheck 10 thetaBelowCell11102213 = true := by
  have h : (thetaBelowCell11102213).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102213 h
theorem e24KC2ThetaBelowLeaf1110222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL thetaBelowCell1110))) = true := by
  have h : ((childHL (childHL (childHL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL thetaBelowCell1110))) = true := by
  have h : ((childHH (childHL (childHL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf111023000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102300) = true := by
  have h : ((childLL thetaBelowCell11102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102300) h
theorem e24KC2ThetaBelowLeaf111023001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102300) = true := by
  have h : ((childLH thetaBelowCell11102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102300) h
theorem e24KC2ThetaBelowLeaf111023002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102300) = true := by
  have h : ((childHL thetaBelowCell11102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102300) h
theorem e24KC2ThetaBelowLeaf111023003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102300) = true := by
  have h : ((childHH thetaBelowCell11102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102300) h
theorem e24KC2ThetaBelowLeaf111023010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102301) = true := by
  have h : ((childLL thetaBelowCell11102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102301) h
theorem e24KC2ThetaBelowLeaf111023011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102301) = true := by
  have h : ((childLH thetaBelowCell11102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102301) h
theorem e24KC2ThetaBelowLeaf111023012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102301) = true := by
  have h : ((childHL thetaBelowCell11102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102301) h
theorem e24KC2ThetaBelowLeaf111023013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102301) = true := by
  have h : ((childHH thetaBelowCell11102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102301) h
theorem e24KC2ThetaBelowLeaf11102302 :
    adaptiveCoverCheck 10 thetaBelowCell11102302 = true := by
  have h : (thetaBelowCell11102302).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102302 h
theorem e24KC2ThetaBelowLeaf11102303 :
    adaptiveCoverCheck 10 thetaBelowCell11102303 = true := by
  have h : (thetaBelowCell11102303).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102303 h
theorem e24KC2ThetaBelowLeaf111023100 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102310) = true := by
  have h : ((childLL thetaBelowCell11102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102310) h
theorem e24KC2ThetaBelowLeaf111023101 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102310) = true := by
  have h : ((childLH thetaBelowCell11102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102310) h
theorem e24KC2ThetaBelowLeaf111023102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102310) = true := by
  have h : ((childHL thetaBelowCell11102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102310) h
theorem e24KC2ThetaBelowLeaf111023103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102310) = true := by
  have h : ((childHH thetaBelowCell11102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102310) h
theorem e24KC2ThetaBelowLeaf111023110 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11102311) = true := by
  have h : ((childLL thetaBelowCell11102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11102311) h
theorem e24KC2ThetaBelowLeaf111023111 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11102311) = true := by
  have h : ((childLH thetaBelowCell11102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11102311) h
theorem e24KC2ThetaBelowLeaf111023112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11102311) = true := by
  have h : ((childHL thetaBelowCell11102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11102311) h
theorem e24KC2ThetaBelowLeaf111023113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11102311) = true := by
  have h : ((childHH thetaBelowCell11102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11102311) h
theorem e24KC2ThetaBelowLeaf11102312 :
    adaptiveCoverCheck 10 thetaBelowCell11102312 = true := by
  have h : (thetaBelowCell11102312).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102312 h
theorem e24KC2ThetaBelowLeaf11102313 :
    adaptiveCoverCheck 10 thetaBelowCell11102313 = true := by
  have h : (thetaBelowCell11102313).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11102313 h
theorem e24KC2ThetaBelowLeaf1110232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL thetaBelowCell1110))) = true := by
  have h : ((childHL (childHH (childHL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL thetaBelowCell1110))) = true := by
  have h : ((childHH (childHH (childHL thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf11103000 :
    adaptiveCoverCheck 10 thetaBelowCell11103000 = true := by
  have h : (thetaBelowCell11103000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103000 h
theorem e24KC2ThetaBelowLeaf11103001 :
    adaptiveCoverCheck 10 thetaBelowCell11103001 = true := by
  have h : (thetaBelowCell11103001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103001 h
theorem e24KC2ThetaBelowLeaf11103002 :
    adaptiveCoverCheck 10 thetaBelowCell11103002 = true := by
  have h : (thetaBelowCell11103002).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103002 h
theorem e24KC2ThetaBelowLeaf11103003 :
    adaptiveCoverCheck 10 thetaBelowCell11103003 = true := by
  have h : (thetaBelowCell11103003).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103003 h
theorem e24KC2ThetaBelowLeaf11103010 :
    adaptiveCoverCheck 10 thetaBelowCell11103010 = true := by
  have h : (thetaBelowCell11103010).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103010 h
theorem e24KC2ThetaBelowLeaf11103011 :
    adaptiveCoverCheck 10 thetaBelowCell11103011 = true := by
  have h : (thetaBelowCell11103011).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103011 h
theorem e24KC2ThetaBelowLeaf11103012 :
    adaptiveCoverCheck 10 thetaBelowCell11103012 = true := by
  have h : (thetaBelowCell11103012).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103012 h
theorem e24KC2ThetaBelowLeaf11103013 :
    adaptiveCoverCheck 10 thetaBelowCell11103013 = true := by
  have h : (thetaBelowCell11103013).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103013 h
theorem e24KC2ThetaBelowLeaf111030200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103020) = true := by
  have h : ((childLL thetaBelowCell11103020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103020) h
theorem e24KC2ThetaBelowLeaf111030201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103020) = true := by
  have h : ((childLH thetaBelowCell11103020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103020) h
theorem e24KC2ThetaBelowLeaf111030202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103020) = true := by
  have h : ((childHL thetaBelowCell11103020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103020) h

end PartE
end GerverSofa

end

end

end
