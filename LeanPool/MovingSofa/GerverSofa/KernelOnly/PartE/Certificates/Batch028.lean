/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchC0ea1b4a6af3d1dc`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC6 explicit proof-producing certificate batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3658ca4972

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111132101020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101020 : AngleCell :=
  childLL (childHL (childLL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101021 : AngleCell :=
  childLH (childHL (childLL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101022 : AngleCell :=
  childHL (childHL (childLL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101023 : AngleCell :=
  childHH (childHL (childLL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101030 : AngleCell :=
  childLL (childHH (childLL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101031 : AngleCell :=
  childLH (childHH (childLL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101032 : AngleCell :=
  childHL (childHH (childLL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101033 : AngleCell :=
  childHH (childHH (childLL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101120 : AngleCell :=
  childLL (childHL (childLH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101121 : AngleCell :=
  childLH (childHL (childLH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101122 : AngleCell :=
  childHL (childHL (childLH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101123 : AngleCell :=
  childHH (childHL (childLH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101130 : AngleCell :=
  childLL (childHH (childLH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101131 : AngleCell :=
  childLH (childHH (childLH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101132 : AngleCell :=
  childHL (childHH (childLH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101133 : AngleCell :=
  childHH (childHH (childLH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell11113210)))
/-- Subcell `111132101300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132101333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132101333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell11113210)))
/-- Subcell `111132110020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110020 : AngleCell :=
  childLL (childHL (childLL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110021 : AngleCell :=
  childLH (childHL (childLL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110022 : AngleCell :=
  childHL (childHL (childLL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110023 : AngleCell :=
  childHH (childHL (childLL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110030 : AngleCell :=
  childLL (childHH (childLL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110031 : AngleCell :=
  childLH (childHH (childLL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110032 : AngleCell :=
  childHL (childHH (childLL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110033 : AngleCell :=
  childHH (childHH (childLL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110120 : AngleCell :=
  childLL (childHL (childLH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110121 : AngleCell :=
  childLH (childHL (childLH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110122 : AngleCell :=
  childHL (childHL (childLH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110123 : AngleCell :=
  childHH (childHL (childLH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110130 : AngleCell :=
  childLL (childHH (childLH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110131 : AngleCell :=
  childLH (childHH (childLH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110132 : AngleCell :=
  childHL (childHH (childLH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110133 : AngleCell :=
  childHH (childHH (childLH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell11113211)))
/-- Subcell `111132110300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132110333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132110333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell11113211)))
/-- Subcell `111132111020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111020 : AngleCell :=
  childLL (childHL (childLL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111021 : AngleCell :=
  childLH (childHL (childLL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111022 : AngleCell :=
  childHL (childHL (childLL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111023 : AngleCell :=
  childHH (childHL (childLL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111030 : AngleCell :=
  childLL (childHH (childLL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111031 : AngleCell :=
  childLH (childHH (childLL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111032 : AngleCell :=
  childHL (childHH (childLL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111033 : AngleCell :=
  childHH (childHH (childLL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111120 : AngleCell :=
  childLL (childHL (childLH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111121 : AngleCell :=
  childLH (childHL (childLH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111122 : AngleCell :=
  childHL (childHL (childLH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111123 : AngleCell :=
  childHH (childHL (childLH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111130 : AngleCell :=
  childLL (childHH (childLH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111131 : AngleCell :=
  childLH (childHH (childLH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111132 : AngleCell :=
  childHL (childHH (childLH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111133 : AngleCell :=
  childHH (childHH (childLH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell11113211)))
/-- Subcell `111132111300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111132111333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell11113211)))
/-- Subcell `111133000020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000020 : AngleCell :=
  childLL (childHL (childLL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000021 : AngleCell :=
  childLH (childHL (childLL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000022 : AngleCell :=
  childHL (childHL (childLL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000023 : AngleCell :=
  childHH (childHL (childLL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000030 : AngleCell :=
  childLL (childHH (childLL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000031 : AngleCell :=
  childLH (childHH (childLL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000032 : AngleCell :=
  childHL (childHH (childLL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000033 : AngleCell :=
  childHH (childHH (childLL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000120 : AngleCell :=
  childLL (childHL (childLH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000121 : AngleCell :=
  childLH (childHL (childLH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000122 : AngleCell :=
  childHL (childHL (childLH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000123 : AngleCell :=
  childHH (childHL (childLH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000130 : AngleCell :=
  childLL (childHH (childLH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000131 : AngleCell :=
  childLH (childHH (childLH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000132 : AngleCell :=
  childHL (childHH (childLH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000133 : AngleCell :=
  childHH (childHH (childLH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell11113300)))
/-- Subcell `111133000300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133000333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133000333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell11113300)))
/-- Subcell `111133001020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001020 : AngleCell :=
  childLL (childHL (childLL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001021 : AngleCell :=
  childLH (childHL (childLL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001022 : AngleCell :=
  childHL (childHL (childLL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001023 : AngleCell :=
  childHH (childHL (childLL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001030 : AngleCell :=
  childLL (childHH (childLL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001031 : AngleCell :=
  childLH (childHH (childLL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001032 : AngleCell :=
  childHL (childHH (childLL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001033 : AngleCell :=
  childHH (childHH (childLL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell11113300)))
/-- Subcell `111133001310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001120 : AngleCell :=
  childLL (childHL (childLH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001121 : AngleCell :=
  childLH (childHL (childLH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001122 : AngleCell :=
  childHL (childHL (childLH (childLH thetaBelowCell11113300)))
/-- Subcell `111133001123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133001123 : AngleCell :=
  childHH (childHL (childLH (childLH thetaBelowCell11113300)))
/-- Subcell `111133002100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell11113300)))
/-- Subcell `111133002101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell11113300)))
/-- Subcell `111133002102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell11113300)))
/-- Subcell `111133002103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell11113300)))
/-- Subcell `111133002110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell11113300)))
/-- Subcell `111133002111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell11113300)))
/-- Subcell `111133002112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell11113300)))
/-- Subcell `111133002113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell11113300)))
/-- Subcell `111133003000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell11113300)))
/-- Subcell `111133003001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell11113300)))
/-- Subcell `111133003002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell11113300)))
/-- Subcell `111133003003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell11113300)))
/-- Subcell `111133003010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell11113300)))
/-- Subcell `111133003011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell11113300)))
/-- Subcell `111133003012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell11113300)))
/-- Subcell `111133003013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell11113300)))
/-- Subcell `111133003100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell11113300)))
/-- Subcell `111133003101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113300)))
/-- Subcell `111133003102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell11113300)))
/-- Subcell `111133003103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell11113300)))
/-- Subcell `111133003110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113300)))
/-- Subcell `111133003111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113300)))
/-- Subcell `111133003112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell11113300)))
/-- Subcell `111133003113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell11113300)))
/-- Subcell `111133010200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell11113301)))
/-- Subcell `111133010300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133010333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133010333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell11113301)))
/-- Subcell `111133011200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell11113301)))
/-- Subcell `111133011300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133011333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133011333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell11113301)))
/-- Subcell `111133012000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell11113301)))
/-- Subcell `111133012001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell11113301)))
/-- Subcell `111133012002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell11113301)))
/-- Subcell `111133012003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell11113301)))
/-- Subcell `111133012010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell11113301)))
/-- Subcell `111133012011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell11113301)))
/-- Subcell `111133012012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell11113301)))
/-- Subcell `111133012013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell11113301)))
/-- Subcell `111133012100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell11113301)))
/-- Subcell `111133012101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell11113301)))
/-- Subcell `111133012102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell11113301)))
/-- Subcell `111133012103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell11113301)))
/-- Subcell `111133012110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell11113301)))
/-- Subcell `111133012111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell11113301)))
/-- Subcell `111133012112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell11113301)))
/-- Subcell `111133012113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell11113301)))
/-- Subcell `111133013000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell11113301)))
/-- Subcell `111133013001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell11113301)))
/-- Subcell `111133013002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell11113301)))
/-- Subcell `111133013003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell11113301)))
/-- Subcell `111133013010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell11113301)))
/-- Subcell `111133013011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell11113301)))
/-- Subcell `111133013012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell11113301)))
/-- Subcell `111133013013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell11113301)))
/-- Subcell `111133013100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell11113301)))
/-- Subcell `111133013101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113301)))
/-- Subcell `111133013102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell11113301)))
/-- Subcell `111133013103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell11113301)))
/-- Subcell `111133013110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113301)))
/-- Subcell `111133013111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113301)))
/-- Subcell `111133013112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell11113301)))
/-- Subcell `111133013113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell11113301)))
/-- Subcell `111133100200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell11113310)))
/-- Subcell `111133100323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133100313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133100313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell11113310)))
/-- Subcell `111133101220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell11113310)))
/-- Subcell `111133101322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133101313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133101313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell11113310)))
/-- Subcell `111133102000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell11113310)))
/-- Subcell `111133102001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell11113310)))
/-- Subcell `111133102002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell11113310)))
/-- Subcell `111133102003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell11113310)))
/-- Subcell `111133102010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell11113310)))
/-- Subcell `111133102011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell11113310)))
/-- Subcell `111133102012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell11113310)))
/-- Subcell `111133102013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell11113310)))
/-- Subcell `111133102100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell11113310)))
/-- Subcell `111133102101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell11113310)))
/-- Subcell `111133102102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell11113310)))
/-- Subcell `111133102103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell11113310)))
/-- Subcell `111133102110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell11113310)))
/-- Subcell `111133102111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell11113310)))
/-- Subcell `111133102112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell11113310)))
/-- Subcell `111133102113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell11113310)))
/-- Subcell `111133103001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell11113310)))
/-- Subcell `111133103000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell11113310)))
/-- Subcell `111133103002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell11113310)))
/-- Subcell `111133103003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell11113310)))
/-- Subcell `111133103010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell11113310)))
/-- Subcell `111133103011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell11113310)))
/-- Subcell `111133103012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell11113310)))
/-- Subcell `111133103013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell11113310)))
/-- Subcell `111133103100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell11113310)))
/-- Subcell `111133103101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113310)))
/-- Subcell `111133103102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell11113310)))
/-- Subcell `111133103103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell11113310)))
/-- Subcell `111133103110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113310)))
/-- Subcell `111133103111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113310)))
/-- Subcell `111133103112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell11113310)))
/-- Subcell `111133103113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell11113310)))

end CertificateCells3658ca4972

open CertificateCells3658ca4972
theorem cover_subtree_c250c0508e67 :
    adaptiveCoverCheck 8 (childLL (childLH thetaBelowCell11113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11113210))
    (by
      have h : ((childLL (childLL (childLH thetaBelowCell11113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
        thetaBelowCell11113210))) h)
    (by
      have h : ((childLH (childLL (childLH thetaBelowCell11113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
        thetaBelowCell11113210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101020 h)
        (by
          have h : (thetaBelowCell111132101021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101021 h)
        (by
          have h : (thetaBelowCell111132101022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101022 h)
        (by
          have h : (thetaBelowCell111132101023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101030 h)
        (by
          have h : (thetaBelowCell111132101031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101031 h)
        (by
          have h : (thetaBelowCell111132101032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101032 h)
        (by
          have h : (thetaBelowCell111132101033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101033 h))

theorem cover_subtree_37f607119182 :
    adaptiveCoverCheck 8 (childLH (childLH thetaBelowCell11113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11113210))
    (by
      have h : ((childLL (childLH (childLH thetaBelowCell11113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
        thetaBelowCell11113210))) h)
    (by
      have h : ((childLH (childLH (childLH thetaBelowCell11113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
        thetaBelowCell11113210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101120 h)
        (by
          have h : (thetaBelowCell111132101121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101121 h)
        (by
          have h : (thetaBelowCell111132101122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101122 h)
        (by
          have h : (thetaBelowCell111132101123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101130 h)
        (by
          have h : (thetaBelowCell111132101131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101131 h)
        (by
          have h : (thetaBelowCell111132101132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101132 h)
        (by
          have h : (thetaBelowCell111132101133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101133 h))

theorem cover_subtree_9b56cbca582c :
    adaptiveCoverCheck 8 (childHL (childLH thetaBelowCell11113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11113210))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101200 h)
        (by
          have h : (thetaBelowCell111132101201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101201 h)
        (by
          have h : (thetaBelowCell111132101202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101202 h)
        (by
          have h : (thetaBelowCell111132101203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101210 h)
        (by
          have h : (thetaBelowCell111132101211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101211 h)
        (by
          have h : (thetaBelowCell111132101212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101212 h)
        (by
          have h : (thetaBelowCell111132101213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101220 h)
        (by
          have h : (thetaBelowCell111132101221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101221 h)
        (by
          have h : (thetaBelowCell111132101222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101222 h)
        (by
          have h : (thetaBelowCell111132101223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101230 h)
        (by
          have h : (thetaBelowCell111132101231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101231 h)
        (by
          have h : (thetaBelowCell111132101232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101232 h)
        (by
          have h : (thetaBelowCell111132101233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101233 h))

theorem cover_subtree_321b06e53dc8 :
    adaptiveCoverCheck 8 (childHH (childLH thetaBelowCell11113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11113210))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101300 h)
        (by
          have h : (thetaBelowCell111132101301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101301 h)
        (by
          have h : (thetaBelowCell111132101302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101302 h)
        (by
          have h : (thetaBelowCell111132101303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101310 h)
        (by
          have h : (thetaBelowCell111132101311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101311 h)
        (by
          have h : (thetaBelowCell111132101312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101312 h)
        (by
          have h : (thetaBelowCell111132101313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101320 h)
        (by
          have h : (thetaBelowCell111132101321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101321 h)
        (by
          have h : (thetaBelowCell111132101322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101322 h)
        (by
          have h : (thetaBelowCell111132101323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132101330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101330 h)
        (by
          have h : (thetaBelowCell111132101331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101331 h)
        (by
          have h : (thetaBelowCell111132101332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101332 h)
        (by
          have h : (thetaBelowCell111132101333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132101333 h))

theorem e24KC2ThetaBelowLeaf111132101 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113210) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113210)
    cover_subtree_c250c0508e67
    cover_subtree_37f607119182
    cover_subtree_9b56cbca582c
    cover_subtree_321b06e53dc8
theorem e24KC2ThetaBelowLeaf111132102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113210) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113210)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL thetaBelowCell11113210))
        (by
          have h : ((childLL (childLL (childHL thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL
            thetaBelowCell11113210))) h)
        (by
          have h : ((childLH (childLL (childHL thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL
            thetaBelowCell11113210))) h)
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL
            thetaBelowCell11113210))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL
            thetaBelowCell11113210))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL thetaBelowCell11113210))
        (by
          have h : ((childLL (childLH (childHL thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL
            thetaBelowCell11113210))) h)
        (by
          have h : ((childLH (childLH (childHL thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL
            thetaBelowCell11113210))) h)
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL
            thetaBelowCell11113210))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL
            thetaBelowCell11113210))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell11113210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113210)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113210)) h)
theorem e24KC2ThetaBelowLeaf111132103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113210) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113210)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH thetaBelowCell11113210))
        (by
          have h : ((childLL (childLL (childHH thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH
            thetaBelowCell11113210))) h)
        (by
          have h : ((childLH (childLL (childHH thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH
            thetaBelowCell11113210))) h)
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH
            thetaBelowCell11113210))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH
            thetaBelowCell11113210))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH thetaBelowCell11113210))
        (by
          have h : ((childLL (childLH (childHH thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH
            thetaBelowCell11113210))) h)
        (by
          have h : ((childLH (childLH (childHH thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH
            thetaBelowCell11113210))) h)
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH
            thetaBelowCell11113210))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell11113210)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH
            thetaBelowCell11113210))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell11113210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113210)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113210)) h)
theorem cover_subtree_c437be4b8029 :
    adaptiveCoverCheck 8 (childLL (childLL thetaBelowCell11113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11113211))
    (by
      have h : ((childLL (childLL (childLL thetaBelowCell11113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
        thetaBelowCell11113211))) h)
    (by
      have h : ((childLH (childLL (childLL thetaBelowCell11113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
        thetaBelowCell11113211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110020 h)
        (by
          have h : (thetaBelowCell111132110021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110021 h)
        (by
          have h : (thetaBelowCell111132110022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110022 h)
        (by
          have h : (thetaBelowCell111132110023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110030 h)
        (by
          have h : (thetaBelowCell111132110031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110031 h)
        (by
          have h : (thetaBelowCell111132110032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110032 h)
        (by
          have h : (thetaBelowCell111132110033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110033 h))

theorem cover_subtree_e1c2184f45cd :
    adaptiveCoverCheck 8 (childLH (childLL thetaBelowCell11113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11113211))
    (by
      have h : ((childLL (childLH (childLL thetaBelowCell11113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
        thetaBelowCell11113211))) h)
    (by
      have h : ((childLH (childLH (childLL thetaBelowCell11113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
        thetaBelowCell11113211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110120 h)
        (by
          have h : (thetaBelowCell111132110121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110121 h)
        (by
          have h : (thetaBelowCell111132110122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110122 h)
        (by
          have h : (thetaBelowCell111132110123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110130 h)
        (by
          have h : (thetaBelowCell111132110131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110131 h)
        (by
          have h : (thetaBelowCell111132110132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110132 h)
        (by
          have h : (thetaBelowCell111132110133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110133 h))

theorem cover_subtree_baaa428341e9 :
    adaptiveCoverCheck 8 (childHL (childLL thetaBelowCell11113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11113211))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110200 h)
        (by
          have h : (thetaBelowCell111132110201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110201 h)
        (by
          have h : (thetaBelowCell111132110202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110202 h)
        (by
          have h : (thetaBelowCell111132110203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110210 h)
        (by
          have h : (thetaBelowCell111132110211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110211 h)
        (by
          have h : (thetaBelowCell111132110212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110212 h)
        (by
          have h : (thetaBelowCell111132110213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110220 h)
        (by
          have h : (thetaBelowCell111132110221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110221 h)
        (by
          have h : (thetaBelowCell111132110222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110222 h)
        (by
          have h : (thetaBelowCell111132110223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110230 h)
        (by
          have h : (thetaBelowCell111132110231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110231 h)
        (by
          have h : (thetaBelowCell111132110232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110232 h)
        (by
          have h : (thetaBelowCell111132110233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110233 h))

theorem cover_subtree_fa56c52c3951 :
    adaptiveCoverCheck 8 (childHH (childLL thetaBelowCell11113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11113211))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110300 h)
        (by
          have h : (thetaBelowCell111132110301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110301 h)
        (by
          have h : (thetaBelowCell111132110302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110302 h)
        (by
          have h : (thetaBelowCell111132110303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110310 h)
        (by
          have h : (thetaBelowCell111132110311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110311 h)
        (by
          have h : (thetaBelowCell111132110312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110312 h)
        (by
          have h : (thetaBelowCell111132110313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110320 h)
        (by
          have h : (thetaBelowCell111132110321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110321 h)
        (by
          have h : (thetaBelowCell111132110322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110322 h)
        (by
          have h : (thetaBelowCell111132110323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132110330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110330 h)
        (by
          have h : (thetaBelowCell111132110331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110331 h)
        (by
          have h : (thetaBelowCell111132110332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110332 h)
        (by
          have h : (thetaBelowCell111132110333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132110333 h))

theorem e24KC2ThetaBelowLeaf111132110 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113211)
    cover_subtree_c437be4b8029
    cover_subtree_e1c2184f45cd
    cover_subtree_baaa428341e9
    cover_subtree_fa56c52c3951
theorem cover_subtree_3dbc5ee0205c :
    adaptiveCoverCheck 8 (childLL (childLH thetaBelowCell11113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11113211))
    (by
      have h : ((childLL (childLL (childLH thetaBelowCell11113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
        thetaBelowCell11113211))) h)
    (by
      have h : ((childLH (childLL (childLH thetaBelowCell11113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
        thetaBelowCell11113211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111020 h)
        (by
          have h : (thetaBelowCell111132111021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111021 h)
        (by
          have h : (thetaBelowCell111132111022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111022 h)
        (by
          have h : (thetaBelowCell111132111023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111030 h)
        (by
          have h : (thetaBelowCell111132111031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111031 h)
        (by
          have h : (thetaBelowCell111132111032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111032 h)
        (by
          have h : (thetaBelowCell111132111033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111033 h))

theorem cover_subtree_63676dfa48d8 :
    adaptiveCoverCheck 8 (childLH (childLH thetaBelowCell11113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11113211))
    (by
      have h : ((childLL (childLH (childLH thetaBelowCell11113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
        thetaBelowCell11113211))) h)
    (by
      have h : ((childLH (childLH (childLH thetaBelowCell11113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
        thetaBelowCell11113211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111120 h)
        (by
          have h : (thetaBelowCell111132111121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111121 h)
        (by
          have h : (thetaBelowCell111132111122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111122 h)
        (by
          have h : (thetaBelowCell111132111123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111130 h)
        (by
          have h : (thetaBelowCell111132111131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111131 h)
        (by
          have h : (thetaBelowCell111132111132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111132 h)
        (by
          have h : (thetaBelowCell111132111133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111133 h))

theorem cover_subtree_27023d7e3233 :
    adaptiveCoverCheck 8 (childHL (childLH thetaBelowCell11113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11113211))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111200 h)
        (by
          have h : (thetaBelowCell111132111201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111201 h)
        (by
          have h : (thetaBelowCell111132111202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111202 h)
        (by
          have h : (thetaBelowCell111132111203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111210 h)
        (by
          have h : (thetaBelowCell111132111211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111211 h)
        (by
          have h : (thetaBelowCell111132111212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111212 h)
        (by
          have h : (thetaBelowCell111132111213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111220 h)
        (by
          have h : (thetaBelowCell111132111221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111221 h)
        (by
          have h : (thetaBelowCell111132111222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111222 h)
        (by
          have h : (thetaBelowCell111132111223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111230 h)
        (by
          have h : (thetaBelowCell111132111231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111231 h)
        (by
          have h : (thetaBelowCell111132111232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111232 h)
        (by
          have h : (thetaBelowCell111132111233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111233 h))

theorem cover_subtree_f383ba4cac40 :
    adaptiveCoverCheck 8 (childHH (childLH thetaBelowCell11113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11113211))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111300 h)
        (by
          have h : (thetaBelowCell111132111301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111301 h)
        (by
          have h : (thetaBelowCell111132111302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111302 h)
        (by
          have h : (thetaBelowCell111132111303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111310 h)
        (by
          have h : (thetaBelowCell111132111311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111311 h)
        (by
          have h : (thetaBelowCell111132111312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111312 h)
        (by
          have h : (thetaBelowCell111132111313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111320 h)
        (by
          have h : (thetaBelowCell111132111321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111321 h)
        (by
          have h : (thetaBelowCell111132111322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111322 h)
        (by
          have h : (thetaBelowCell111132111323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH
        thetaBelowCell11113211)))
        (by
          have h : (thetaBelowCell111132111330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111330 h)
        (by
          have h : (thetaBelowCell111132111331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111331 h)
        (by
          have h : (thetaBelowCell111132111332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111332 h)
        (by
          have h : (thetaBelowCell111132111333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132111333 h))

theorem e24KC2ThetaBelowLeaf111132111 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113211)
    cover_subtree_3dbc5ee0205c
    cover_subtree_63676dfa48d8
    cover_subtree_27023d7e3233
    cover_subtree_f383ba4cac40
theorem e24KC2ThetaBelowLeaf111132112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113211)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL thetaBelowCell11113211))
        (by
          have h : ((childLL (childLL (childHL thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL
            thetaBelowCell11113211))) h)
        (by
          have h : ((childLH (childLL (childHL thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL
            thetaBelowCell11113211))) h)
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL
            thetaBelowCell11113211))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL
            thetaBelowCell11113211))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL thetaBelowCell11113211))
        (by
          have h : ((childLL (childLH (childHL thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL
            thetaBelowCell11113211))) h)
        (by
          have h : ((childLH (childLH (childHL thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL
            thetaBelowCell11113211))) h)
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL
            thetaBelowCell11113211))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL
            thetaBelowCell11113211))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell11113211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113211)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113211)) h)
theorem e24KC2ThetaBelowLeaf111132113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113211)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH thetaBelowCell11113211))
        (by
          have h : ((childLL (childLL (childHH thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH
            thetaBelowCell11113211))) h)
        (by
          have h : ((childLH (childLL (childHH thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH
            thetaBelowCell11113211))) h)
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH
            thetaBelowCell11113211))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH
            thetaBelowCell11113211))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH thetaBelowCell11113211))
        (by
          have h : ((childLL (childLH (childHH thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH
            thetaBelowCell11113211))) h)
        (by
          have h : ((childLH (childLH (childHH thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH
            thetaBelowCell11113211))) h)
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH
            thetaBelowCell11113211))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell11113211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH
            thetaBelowCell11113211))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell11113211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113211)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113211)) h)
theorem cover_subtree_2d104ae8510a :
    adaptiveCoverCheck 8 (childLL (childLL thetaBelowCell11113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11113300))
    (by
      have h : ((childLL (childLL (childLL thetaBelowCell11113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
        thetaBelowCell11113300))) h)
    (by
      have h : ((childLH (childLL (childLL thetaBelowCell11113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
        thetaBelowCell11113300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000020 h)
        (by
          have h : (thetaBelowCell111133000021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000021 h)
        (by
          have h : (thetaBelowCell111133000022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000022 h)
        (by
          have h : (thetaBelowCell111133000023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000030 h)
        (by
          have h : (thetaBelowCell111133000031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000031 h)
        (by
          have h : (thetaBelowCell111133000032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000032 h)
        (by
          have h : (thetaBelowCell111133000033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000033 h))

theorem cover_subtree_73e80951f42f :
    adaptiveCoverCheck 8 (childLH (childLL thetaBelowCell11113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11113300))
    (by
      have h : ((childLL (childLH (childLL thetaBelowCell11113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
        thetaBelowCell11113300))) h)
    (by
      have h : ((childLH (childLH (childLL thetaBelowCell11113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
        thetaBelowCell11113300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000120 h)
        (by
          have h : (thetaBelowCell111133000121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000121 h)
        (by
          have h : (thetaBelowCell111133000122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000122 h)
        (by
          have h : (thetaBelowCell111133000123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000130 h)
        (by
          have h : (thetaBelowCell111133000131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000131 h)
        (by
          have h : (thetaBelowCell111133000132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000132 h)
        (by
          have h : (thetaBelowCell111133000133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000133 h))

theorem cover_subtree_788fa0ec2ac5 :
    adaptiveCoverCheck 8 (childHL (childLL thetaBelowCell11113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11113300))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000200 h)
        (by
          have h : (thetaBelowCell111133000201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000201 h)
        (by
          have h : (thetaBelowCell111133000202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000202 h)
        (by
          have h : (thetaBelowCell111133000203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000210 h)
        (by
          have h : (thetaBelowCell111133000211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000211 h)
        (by
          have h : (thetaBelowCell111133000212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000212 h)
        (by
          have h : (thetaBelowCell111133000213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000220 h)
        (by
          have h : (thetaBelowCell111133000221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000221 h)
        (by
          have h : (thetaBelowCell111133000222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000222 h)
        (by
          have h : (thetaBelowCell111133000223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000230 h)
        (by
          have h : (thetaBelowCell111133000231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000231 h)
        (by
          have h : (thetaBelowCell111133000232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000232 h)
        (by
          have h : (thetaBelowCell111133000233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000233 h))

theorem cover_subtree_a895dbe70eef :
    adaptiveCoverCheck 8 (childHH (childLL thetaBelowCell11113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11113300))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000300 h)
        (by
          have h : (thetaBelowCell111133000301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000301 h)
        (by
          have h : (thetaBelowCell111133000302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000302 h)
        (by
          have h : (thetaBelowCell111133000303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000310 h)
        (by
          have h : (thetaBelowCell111133000311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000311 h)
        (by
          have h : (thetaBelowCell111133000312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000312 h)
        (by
          have h : (thetaBelowCell111133000313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000320 h)
        (by
          have h : (thetaBelowCell111133000321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000321 h)
        (by
          have h : (thetaBelowCell111133000322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000322 h)
        (by
          have h : (thetaBelowCell111133000323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133000330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000330 h)
        (by
          have h : (thetaBelowCell111133000331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000331 h)
        (by
          have h : (thetaBelowCell111133000332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000332 h)
        (by
          have h : (thetaBelowCell111133000333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133000333 h))

theorem e24KC2ThetaBelowLeaf111133000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113300)
    cover_subtree_2d104ae8510a
    cover_subtree_73e80951f42f
    cover_subtree_788fa0ec2ac5
    cover_subtree_a895dbe70eef
theorem cover_subtree_f0725b4a5e12 :
    adaptiveCoverCheck 8 (childLL (childLH thetaBelowCell11113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11113300))
    (by
      have h : ((childLL (childLL (childLH thetaBelowCell11113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
        thetaBelowCell11113300))) h)
    (by
      have h : ((childLH (childLL (childLH thetaBelowCell11113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
        thetaBelowCell11113300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133001020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001020 h)
        (by
          have h : (thetaBelowCell111133001021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001021 h)
        (by
          have h : (thetaBelowCell111133001022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001022 h)
        (by
          have h : (thetaBelowCell111133001023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133001030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001030 h)
        (by
          have h : (thetaBelowCell111133001031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001031 h)
        (by
          have h : (thetaBelowCell111133001032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001032 h)
        (by
          have h : (thetaBelowCell111133001033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001033 h))

theorem cover_subtree_cedab414430b :
    adaptiveCoverCheck 7 (childHL (childHL (childLH thetaBelowCell11113300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH thetaBelowCell11113300)))
    (by
      have h : (thetaBelowCell111133001220).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001220 h)
    (by
      have h : (thetaBelowCell111133001221).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001221 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001222
        (by
          have h : ((childLL thetaBelowCell111133001222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001222) h)
        (by
          have h : ((childLH thetaBelowCell111133001222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001222) h)
        (by
          have h : ((childHL thetaBelowCell111133001222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001222) h)
        (by
          have h : ((childHH thetaBelowCell111133001222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001223
        (by
          have h : ((childLL thetaBelowCell111133001223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001223) h)
        (by
          have h : ((childLH thetaBelowCell111133001223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001223) h)
        (by
          have h : ((childHL thetaBelowCell111133001223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001223) h)
        (by
          have h : ((childHH thetaBelowCell111133001223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001223) h))

theorem cover_subtree_15d931d0b831 :
    adaptiveCoverCheck 7 (childHH (childHL (childLH thetaBelowCell11113300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH thetaBelowCell11113300)))
    (by
      have h : (thetaBelowCell111133001230).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001230 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001231
        (by
          have h : ((childLL thetaBelowCell111133001231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001231) h)
        (by
          have h : ((childLH thetaBelowCell111133001231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001231) h)
        (by
          have h : ((childHL thetaBelowCell111133001231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001231) h)
        (by
          have h : ((childHH thetaBelowCell111133001231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001232
        (by
          have h : ((childLL thetaBelowCell111133001232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001232) h)
        (by
          have h : ((childLH thetaBelowCell111133001232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001232) h)
        (by
          have h : ((childHL thetaBelowCell111133001232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001232) h)
        (by
          have h : ((childHH thetaBelowCell111133001232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001233
        (by
          have h : ((childLL thetaBelowCell111133001233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001233) h)
        (by
          have h : ((childLH thetaBelowCell111133001233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001233) h)
        (by
          have h : ((childHL thetaBelowCell111133001233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001233) h)
        (by
          have h : ((childHH thetaBelowCell111133001233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001233) h))

theorem cover_subtree_4398f73b5a5d :
    adaptiveCoverCheck 8 (childHL (childLH thetaBelowCell11113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11113300))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133001200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001200 h)
        (by
          have h : (thetaBelowCell111133001201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001201 h)
        (by
          have h : (thetaBelowCell111133001202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001202 h)
        (by
          have h : (thetaBelowCell111133001203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133001210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001210 h)
        (by
          have h : (thetaBelowCell111133001211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001211 h)
        (by
          have h : (thetaBelowCell111133001212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001212 h)
        (by
          have h : (thetaBelowCell111133001213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001213 h))
    cover_subtree_cedab414430b
    cover_subtree_15d931d0b831

theorem cover_subtree_947341870459 :
    adaptiveCoverCheck 7 (childLH (childHH (childLH thetaBelowCell11113300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH thetaBelowCell11113300)))
    (by
      have h : (thetaBelowCell111133001310).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001310 h)
    (by
      have h : (thetaBelowCell111133001311).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001311 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001312
        (by
          have h : ((childLL thetaBelowCell111133001312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001312) h)
        (by
          have h : ((childLH thetaBelowCell111133001312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001312) h)
        (by
          have h : ((childHL thetaBelowCell111133001312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001312) h)
        (by
          have h : ((childHH thetaBelowCell111133001312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001312) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001313
        (by
          have h : ((childLL thetaBelowCell111133001313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001313) h)
        (by
          have h : ((childLH thetaBelowCell111133001313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001313) h)
        (by
          have h : ((childHL thetaBelowCell111133001313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001313) h)
        (by
          have h : ((childHH thetaBelowCell111133001313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001313) h))

theorem cover_subtree_28ced15c6953 :
    adaptiveCoverCheck 7 (childHL (childHH (childLH thetaBelowCell11113300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH thetaBelowCell11113300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001320
        (by
          have h : ((childLL thetaBelowCell111133001320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001320) h)
        (by
          have h : ((childLH thetaBelowCell111133001320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001320) h)
        (by
          have h : ((childHL thetaBelowCell111133001320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001320) h)
        (by
          have h : ((childHH thetaBelowCell111133001320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001321
        (by
          have h : ((childLL thetaBelowCell111133001321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001321) h)
        (by
          have h : ((childLH thetaBelowCell111133001321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001321) h)
        (by
          have h : ((childHL thetaBelowCell111133001321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001321) h)
        (by
          have h : ((childHH thetaBelowCell111133001321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001321) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001322
        (by
          have h : ((childLL thetaBelowCell111133001322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001322) h)
        (by
          have h : ((childLH thetaBelowCell111133001322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001322) h)
        (by
          have h : ((childHL thetaBelowCell111133001322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001322) h)
        (by
          have h : ((childHH thetaBelowCell111133001322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001322) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001323
        (by
          have h : ((childLL thetaBelowCell111133001323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001323) h)
        (by
          have h : ((childLH thetaBelowCell111133001323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001323) h)
        (by
          have h : ((childHL thetaBelowCell111133001323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001323) h)
        (by
          have h : ((childHH thetaBelowCell111133001323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001323) h))

theorem cover_subtree_440561389a75 :
    adaptiveCoverCheck 7 (childHH (childHH (childLH thetaBelowCell11113300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH thetaBelowCell11113300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001330
        (by
          have h : ((childLL thetaBelowCell111133001330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001330) h)
        (by
          have h : ((childLH thetaBelowCell111133001330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001330) h)
        (by
          have h : ((childHL thetaBelowCell111133001330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001330) h)
        (by
          have h : ((childHH thetaBelowCell111133001330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001331
        (by
          have h : ((childLL thetaBelowCell111133001331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001331) h)
        (by
          have h : ((childLH thetaBelowCell111133001331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001331) h)
        (by
          have h : ((childHL thetaBelowCell111133001331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001331) h)
        (by
          have h : ((childHH thetaBelowCell111133001331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001331) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001332
        (by
          have h : ((childLL thetaBelowCell111133001332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001332) h)
        (by
          have h : ((childLH thetaBelowCell111133001332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001332) h)
        (by
          have h : ((childHL thetaBelowCell111133001332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001332) h)
        (by
          have h : ((childHH thetaBelowCell111133001332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001333
        (by
          have h : ((childLL thetaBelowCell111133001333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001333) h)
        (by
          have h : ((childLH thetaBelowCell111133001333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001333) h)
        (by
          have h : ((childHL thetaBelowCell111133001333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001333) h)
        (by
          have h : ((childHH thetaBelowCell111133001333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001333) h))

theorem cover_subtree_42d3bf5965e9 :
    adaptiveCoverCheck 8 (childHH (childLH thetaBelowCell11113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11113300))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH
        thetaBelowCell11113300)))
        (by
          have h : (thetaBelowCell111133001300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001300 h)
        (by
          have h : (thetaBelowCell111133001301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001301 h)
        (by
          have h : (thetaBelowCell111133001302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001302 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133001303
            (by
              have h : ((childLL thetaBelowCell111133001303)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133001303) h)
            (by
              have h : ((childLH thetaBelowCell111133001303)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133001303) h)
            (by
              have h : ((childHL thetaBelowCell111133001303)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133001303) h)
            (by
              have h : ((childHH thetaBelowCell111133001303)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133001303) h)))
    cover_subtree_947341870459
    cover_subtree_28ced15c6953
    cover_subtree_440561389a75

theorem e24KC2ThetaBelowLeaf111133001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113300)
    cover_subtree_f0725b4a5e12
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11113300))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11113300))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11113300))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH
            thetaBelowCell11113300)))
            (by
              have h : (thetaBelowCell111133001120).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001120 h)
            (by
              have h : (thetaBelowCell111133001121).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001121 h)
            (by
              have h : (thetaBelowCell111133001122).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001122 h)
            (by
              have h : (thetaBelowCell111133001123).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133001123 h))
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11113300))) h))
    cover_subtree_4398f73b5a5d
    cover_subtree_42d3bf5965e9
theorem e24KC2ThetaBelowLeaf111133002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113300)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL thetaBelowCell11113300))
        (by
          have h : ((childLL (childLL (childHL thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL
            thetaBelowCell11113300))) h)
        (by
          have h : ((childLH (childLL (childHL thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL
            thetaBelowCell11113300))) h)
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL
            thetaBelowCell11113300))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL
            thetaBelowCell11113300))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL thetaBelowCell11113300))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHL
            thetaBelowCell11113300)))
            (by
              have h : (thetaBelowCell111133002100).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133002100 h)
            (by
              have h : (thetaBelowCell111133002101).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133002101 h)
            (by
              have h : (thetaBelowCell111133002102).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133002102 h)
            (by
              have h : (thetaBelowCell111133002103).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133002103 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHL
            thetaBelowCell11113300)))
            (by
              have h : (thetaBelowCell111133002110).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133002110 h)
            (by
              have h : (thetaBelowCell111133002111).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133002111 h)
            (by
              have h : (thetaBelowCell111133002112).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133002112 h)
            (by
              have h : (thetaBelowCell111133002113).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133002113 h))
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL
            thetaBelowCell11113300))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL
            thetaBelowCell11113300))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell11113300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113300)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113300)) h)
theorem e24KC2ThetaBelowLeaf111133003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113300)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH thetaBelowCell11113300))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHH
            thetaBelowCell11113300)))
            (by
              have h : (thetaBelowCell111133003000).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003000 h)
            (by
              have h : (thetaBelowCell111133003001).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003001 h)
            (by
              have h : (thetaBelowCell111133003002).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003002 h)
            (by
              have h : (thetaBelowCell111133003003).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003003 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHH
            thetaBelowCell11113300)))
            (by
              have h : (thetaBelowCell111133003010).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003010 h)
            (by
              have h : (thetaBelowCell111133003011).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003011 h)
            (by
              have h : (thetaBelowCell111133003012).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003012 h)
            (by
              have h : (thetaBelowCell111133003013).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003013 h))
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH
            thetaBelowCell11113300))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH
            thetaBelowCell11113300))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH thetaBelowCell11113300))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHH
            thetaBelowCell11113300)))
            (by
              have h : (thetaBelowCell111133003100).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003100 h)
            (by
              have h : (thetaBelowCell111133003101).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003101 h)
            (by
              have h : (thetaBelowCell111133003102).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003102 h)
            (by
              have h : (thetaBelowCell111133003103).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003103 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHH
            thetaBelowCell11113300)))
            (by
              have h : (thetaBelowCell111133003110).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003110 h)
            (by
              have h : (thetaBelowCell111133003111).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003111 h)
            (by
              have h : (thetaBelowCell111133003112).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003112 h)
            (by
              have h : (thetaBelowCell111133003113).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133003113 h))
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH
            thetaBelowCell11113300))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell11113300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH
            thetaBelowCell11113300))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell11113300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113300)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113300)) h)
theorem cover_subtree_37babc6363e9 :
    adaptiveCoverCheck 7 (childLL (childHL (childLL thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL thetaBelowCell11113301)))
    (by
      have h : (thetaBelowCell111133010200).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133010200 h)
    (by
      have h : (thetaBelowCell111133010201).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133010201 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010202
        (by
          have h : ((childLL thetaBelowCell111133010202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010202) h)
        (by
          have h : ((childLH thetaBelowCell111133010202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010202) h)
        (by
          have h : ((childHL thetaBelowCell111133010202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010202) h)
        (by
          have h : ((childHH thetaBelowCell111133010202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010202) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010203
        (by
          have h : ((childLL thetaBelowCell111133010203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010203) h)
        (by
          have h : ((childLH thetaBelowCell111133010203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010203) h)
        (by
          have h : ((childHL thetaBelowCell111133010203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010203) h)
        (by
          have h : ((childHH thetaBelowCell111133010203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010203) h))

theorem cover_subtree_507281a99f13 :
    adaptiveCoverCheck 7 (childLH (childHL (childLL thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL thetaBelowCell11113301)))
    (by
      have h : (thetaBelowCell111133010210).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133010210 h)
    (by
      have h : (thetaBelowCell111133010211).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133010211 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010212
        (by
          have h : ((childLL thetaBelowCell111133010212)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010212) h)
        (by
          have h : ((childLH thetaBelowCell111133010212)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010212) h)
        (by
          have h : ((childHL thetaBelowCell111133010212)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010212) h)
        (by
          have h : ((childHH thetaBelowCell111133010212)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010212) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010213
        (by
          have h : ((childLL thetaBelowCell111133010213)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010213) h)
        (by
          have h : ((childLH thetaBelowCell111133010213)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010213) h)
        (by
          have h : ((childHL thetaBelowCell111133010213)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010213) h)
        (by
          have h : ((childHH thetaBelowCell111133010213)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010213) h))

theorem cover_subtree_a5c13fd746d7 :
    adaptiveCoverCheck 7 (childHL (childHL (childLL thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL thetaBelowCell11113301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010220
        (by
          have h : ((childLL thetaBelowCell111133010220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010220) h)
        (by
          have h : ((childLH thetaBelowCell111133010220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010220) h)
        (by
          have h : ((childHL thetaBelowCell111133010220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010220) h)
        (by
          have h : ((childHH thetaBelowCell111133010220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010220) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010221
        (by
          have h : ((childLL thetaBelowCell111133010221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010221) h)
        (by
          have h : ((childLH thetaBelowCell111133010221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010221) h)
        (by
          have h : ((childHL thetaBelowCell111133010221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010221) h)
        (by
          have h : ((childHH thetaBelowCell111133010221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010221) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010222
        (by
          have h : ((childLL thetaBelowCell111133010222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010222) h)
        (by
          have h : ((childLH thetaBelowCell111133010222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010222) h)
        (by
          have h : ((childHL thetaBelowCell111133010222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010222) h)
        (by
          have h : ((childHH thetaBelowCell111133010222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010223
        (by
          have h : ((childLL thetaBelowCell111133010223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010223) h)
        (by
          have h : ((childLH thetaBelowCell111133010223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010223) h)
        (by
          have h : ((childHL thetaBelowCell111133010223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010223) h)
        (by
          have h : ((childHH thetaBelowCell111133010223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010223) h))

theorem cover_subtree_6d4cbcd8b0bf :
    adaptiveCoverCheck 7 (childHH (childHL (childLL thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL thetaBelowCell11113301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010230
        (by
          have h : ((childLL thetaBelowCell111133010230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010230) h)
        (by
          have h : ((childLH thetaBelowCell111133010230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010230) h)
        (by
          have h : ((childHL thetaBelowCell111133010230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010230) h)
        (by
          have h : ((childHH thetaBelowCell111133010230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010230) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010231
        (by
          have h : ((childLL thetaBelowCell111133010231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010231) h)
        (by
          have h : ((childLH thetaBelowCell111133010231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010231) h)
        (by
          have h : ((childHL thetaBelowCell111133010231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010231) h)
        (by
          have h : ((childHH thetaBelowCell111133010231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010232
        (by
          have h : ((childLL thetaBelowCell111133010232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010232) h)
        (by
          have h : ((childLH thetaBelowCell111133010232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010232) h)
        (by
          have h : ((childHL thetaBelowCell111133010232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010232) h)
        (by
          have h : ((childHH thetaBelowCell111133010232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010233
        (by
          have h : ((childLL thetaBelowCell111133010233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010233) h)
        (by
          have h : ((childLH thetaBelowCell111133010233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010233) h)
        (by
          have h : ((childHL thetaBelowCell111133010233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010233) h)
        (by
          have h : ((childHH thetaBelowCell111133010233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010233) h))

theorem cover_subtree_3b5ec2cd76c2 :
    adaptiveCoverCheck 8 (childHL (childLL thetaBelowCell11113301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11113301))
    cover_subtree_37babc6363e9
    cover_subtree_507281a99f13
    cover_subtree_a5c13fd746d7
    cover_subtree_6d4cbcd8b0bf

theorem cover_subtree_a6f74a199082 :
    adaptiveCoverCheck 7 (childLL (childHH (childLL thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL thetaBelowCell11113301)))
    (by
      have h : (thetaBelowCell111133010300).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133010300 h)
    (by
      have h : (thetaBelowCell111133010301).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133010301 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010302
        (by
          have h : ((childLL thetaBelowCell111133010302)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010302) h)
        (by
          have h : ((childLH thetaBelowCell111133010302)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010302) h)
        (by
          have h : ((childHL thetaBelowCell111133010302)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010302) h)
        (by
          have h : ((childHH thetaBelowCell111133010302)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010302) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010303
        (by
          have h : ((childLL thetaBelowCell111133010303)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010303) h)
        (by
          have h : ((childLH thetaBelowCell111133010303)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010303) h)
        (by
          have h : ((childHL thetaBelowCell111133010303)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010303) h)
        (by
          have h : ((childHH thetaBelowCell111133010303)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010303) h))

theorem cover_subtree_9f6cabcef004 :
    adaptiveCoverCheck 7 (childLH (childHH (childLL thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL thetaBelowCell11113301)))
    (by
      have h : (thetaBelowCell111133010310).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133010310 h)
    (by
      have h : (thetaBelowCell111133010311).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133010311 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010312
        (by
          have h : ((childLL thetaBelowCell111133010312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010312) h)
        (by
          have h : ((childLH thetaBelowCell111133010312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010312) h)
        (by
          have h : ((childHL thetaBelowCell111133010312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010312) h)
        (by
          have h : ((childHH thetaBelowCell111133010312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010312) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010313
        (by
          have h : ((childLL thetaBelowCell111133010313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010313) h)
        (by
          have h : ((childLH thetaBelowCell111133010313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010313) h)
        (by
          have h : ((childHL thetaBelowCell111133010313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010313) h)
        (by
          have h : ((childHH thetaBelowCell111133010313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010313) h))

theorem cover_subtree_66d25ab1916a :
    adaptiveCoverCheck 7 (childHL (childHH (childLL thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL thetaBelowCell11113301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010320
        (by
          have h : ((childLL thetaBelowCell111133010320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010320) h)
        (by
          have h : ((childLH thetaBelowCell111133010320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010320) h)
        (by
          have h : ((childHL thetaBelowCell111133010320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010320) h)
        (by
          have h : ((childHH thetaBelowCell111133010320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010321
        (by
          have h : ((childLL thetaBelowCell111133010321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010321) h)
        (by
          have h : ((childLH thetaBelowCell111133010321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010321) h)
        (by
          have h : ((childHL thetaBelowCell111133010321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010321) h)
        (by
          have h : ((childHH thetaBelowCell111133010321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010321) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010322
        (by
          have h : ((childLL thetaBelowCell111133010322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010322) h)
        (by
          have h : ((childLH thetaBelowCell111133010322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010322) h)
        (by
          have h : ((childHL thetaBelowCell111133010322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010322) h)
        (by
          have h : ((childHH thetaBelowCell111133010322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010322) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010323
        (by
          have h : ((childLL thetaBelowCell111133010323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010323) h)
        (by
          have h : ((childLH thetaBelowCell111133010323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010323) h)
        (by
          have h : ((childHL thetaBelowCell111133010323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010323) h)
        (by
          have h : ((childHH thetaBelowCell111133010323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010323) h))

theorem cover_subtree_7a16ff7db42a :
    adaptiveCoverCheck 7 (childHH (childHH (childLL thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL thetaBelowCell11113301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010330
        (by
          have h : ((childLL thetaBelowCell111133010330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010330) h)
        (by
          have h : ((childLH thetaBelowCell111133010330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010330) h)
        (by
          have h : ((childHL thetaBelowCell111133010330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010330) h)
        (by
          have h : ((childHH thetaBelowCell111133010330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010331
        (by
          have h : ((childLL thetaBelowCell111133010331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010331) h)
        (by
          have h : ((childLH thetaBelowCell111133010331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010331) h)
        (by
          have h : ((childHL thetaBelowCell111133010331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010331) h)
        (by
          have h : ((childHH thetaBelowCell111133010331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010331) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010332
        (by
          have h : ((childLL thetaBelowCell111133010332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010332) h)
        (by
          have h : ((childLH thetaBelowCell111133010332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010332) h)
        (by
          have h : ((childHL thetaBelowCell111133010332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010332) h)
        (by
          have h : ((childHH thetaBelowCell111133010332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133010333
        (by
          have h : ((childLL thetaBelowCell111133010333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133010333) h)
        (by
          have h : ((childLH thetaBelowCell111133010333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133010333) h)
        (by
          have h : ((childHL thetaBelowCell111133010333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133010333) h)
        (by
          have h : ((childHH thetaBelowCell111133010333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133010333) h))

theorem cover_subtree_c3eeff28e7cb :
    adaptiveCoverCheck 8 (childHH (childLL thetaBelowCell11113301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11113301))
    cover_subtree_a6f74a199082
    cover_subtree_9f6cabcef004
    cover_subtree_66d25ab1916a
    cover_subtree_7a16ff7db42a

theorem e24KC2ThetaBelowLeaf111133010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113301)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11113301))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11113301))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11113301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11113301))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11113301))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11113301))) h))
    cover_subtree_3b5ec2cd76c2
    cover_subtree_c3eeff28e7cb
theorem cover_subtree_1ae28d021e20 :
    adaptiveCoverCheck 7 (childLL (childHL (childLH thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH thetaBelowCell11113301)))
    (by
      have h : (thetaBelowCell111133011200).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133011200 h)
    (by
      have h : (thetaBelowCell111133011201).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133011201 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011202
        (by
          have h : ((childLL thetaBelowCell111133011202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011202) h)
        (by
          have h : ((childLH thetaBelowCell111133011202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011202) h)
        (by
          have h : ((childHL thetaBelowCell111133011202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011202) h)
        (by
          have h : ((childHH thetaBelowCell111133011202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011202) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011203
        (by
          have h : ((childLL thetaBelowCell111133011203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011203) h)
        (by
          have h : ((childLH thetaBelowCell111133011203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011203) h)
        (by
          have h : ((childHL thetaBelowCell111133011203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011203) h)
        (by
          have h : ((childHH thetaBelowCell111133011203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011203) h))

theorem cover_subtree_40cb4ec2b408 :
    adaptiveCoverCheck 7 (childLH (childHL (childLH thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH thetaBelowCell11113301)))
    (by
      have h : (thetaBelowCell111133011210).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133011210 h)
    (by
      have h : (thetaBelowCell111133011211).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133011211 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011212
        (by
          have h : ((childLL thetaBelowCell111133011212)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011212) h)
        (by
          have h : ((childLH thetaBelowCell111133011212)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011212) h)
        (by
          have h : ((childHL thetaBelowCell111133011212)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011212) h)
        (by
          have h : ((childHH thetaBelowCell111133011212)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011212) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011213
        (by
          have h : ((childLL thetaBelowCell111133011213)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011213) h)
        (by
          have h : ((childLH thetaBelowCell111133011213)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011213) h)
        (by
          have h : ((childHL thetaBelowCell111133011213)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011213) h)
        (by
          have h : ((childHH thetaBelowCell111133011213)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011213) h))

theorem cover_subtree_b87befd4bfbe :
    adaptiveCoverCheck 7 (childHL (childHL (childLH thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH thetaBelowCell11113301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011220
        (by
          have h : ((childLL thetaBelowCell111133011220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011220) h)
        (by
          have h : ((childLH thetaBelowCell111133011220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011220) h)
        (by
          have h : ((childHL thetaBelowCell111133011220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011220) h)
        (by
          have h : ((childHH thetaBelowCell111133011220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011220) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011221
        (by
          have h : ((childLL thetaBelowCell111133011221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011221) h)
        (by
          have h : ((childLH thetaBelowCell111133011221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011221) h)
        (by
          have h : ((childHL thetaBelowCell111133011221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011221) h)
        (by
          have h : ((childHH thetaBelowCell111133011221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011221) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011222
        (by
          have h : ((childLL thetaBelowCell111133011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011222) h)
        (by
          have h : ((childLH thetaBelowCell111133011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011222) h)
        (by
          have h : ((childHL thetaBelowCell111133011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011222) h)
        (by
          have h : ((childHH thetaBelowCell111133011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011223
        (by
          have h : ((childLL thetaBelowCell111133011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011223) h)
        (by
          have h : ((childLH thetaBelowCell111133011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011223) h)
        (by
          have h : ((childHL thetaBelowCell111133011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011223) h)
        (by
          have h : ((childHH thetaBelowCell111133011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011223) h))

theorem cover_subtree_58527e6cb5e3 :
    adaptiveCoverCheck 7 (childHH (childHL (childLH thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH thetaBelowCell11113301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011230
        (by
          have h : ((childLL thetaBelowCell111133011230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011230) h)
        (by
          have h : ((childLH thetaBelowCell111133011230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011230) h)
        (by
          have h : ((childHL thetaBelowCell111133011230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011230) h)
        (by
          have h : ((childHH thetaBelowCell111133011230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011230) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011231
        (by
          have h : ((childLL thetaBelowCell111133011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011231) h)
        (by
          have h : ((childLH thetaBelowCell111133011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011231) h)
        (by
          have h : ((childHL thetaBelowCell111133011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011231) h)
        (by
          have h : ((childHH thetaBelowCell111133011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011232
        (by
          have h : ((childLL thetaBelowCell111133011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011232) h)
        (by
          have h : ((childLH thetaBelowCell111133011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011232) h)
        (by
          have h : ((childHL thetaBelowCell111133011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011232) h)
        (by
          have h : ((childHH thetaBelowCell111133011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011233
        (by
          have h : ((childLL thetaBelowCell111133011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011233) h)
        (by
          have h : ((childLH thetaBelowCell111133011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011233) h)
        (by
          have h : ((childHL thetaBelowCell111133011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011233) h)
        (by
          have h : ((childHH thetaBelowCell111133011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011233) h))

theorem cover_subtree_c56ac23b21bd :
    adaptiveCoverCheck 8 (childHL (childLH thetaBelowCell11113301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11113301))
    cover_subtree_1ae28d021e20
    cover_subtree_40cb4ec2b408
    cover_subtree_b87befd4bfbe
    cover_subtree_58527e6cb5e3

theorem cover_subtree_644ffb1207bc :
    adaptiveCoverCheck 7 (childLL (childHH (childLH thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH thetaBelowCell11113301)))
    (by
      have h : (thetaBelowCell111133011300).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133011300 h)
    (by
      have h : (thetaBelowCell111133011301).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133011301 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011302
        (by
          have h : ((childLL thetaBelowCell111133011302)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011302) h)
        (by
          have h : ((childLH thetaBelowCell111133011302)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011302) h)
        (by
          have h : ((childHL thetaBelowCell111133011302)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011302) h)
        (by
          have h : ((childHH thetaBelowCell111133011302)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011302) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011303
        (by
          have h : ((childLL thetaBelowCell111133011303)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011303) h)
        (by
          have h : ((childLH thetaBelowCell111133011303)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011303) h)
        (by
          have h : ((childHL thetaBelowCell111133011303)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011303) h)
        (by
          have h : ((childHH thetaBelowCell111133011303)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011303) h))

theorem cover_subtree_15868ac019bc :
    adaptiveCoverCheck 7 (childLH (childHH (childLH thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH thetaBelowCell11113301)))
    (by
      have h : (thetaBelowCell111133011310).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133011310 h)
    (by
      have h : (thetaBelowCell111133011311).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133011311 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011312
        (by
          have h : ((childLL thetaBelowCell111133011312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011312) h)
        (by
          have h : ((childLH thetaBelowCell111133011312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011312) h)
        (by
          have h : ((childHL thetaBelowCell111133011312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011312) h)
        (by
          have h : ((childHH thetaBelowCell111133011312)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011312) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011313
        (by
          have h : ((childLL thetaBelowCell111133011313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011313) h)
        (by
          have h : ((childLH thetaBelowCell111133011313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011313) h)
        (by
          have h : ((childHL thetaBelowCell111133011313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011313) h)
        (by
          have h : ((childHH thetaBelowCell111133011313)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011313) h))

theorem cover_subtree_c4a4ddefa402 :
    adaptiveCoverCheck 7 (childHL (childHH (childLH thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH thetaBelowCell11113301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011320
        (by
          have h : ((childLL thetaBelowCell111133011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011320) h)
        (by
          have h : ((childLH thetaBelowCell111133011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011320) h)
        (by
          have h : ((childHL thetaBelowCell111133011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011320) h)
        (by
          have h : ((childHH thetaBelowCell111133011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011321
        (by
          have h : ((childLL thetaBelowCell111133011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011321) h)
        (by
          have h : ((childLH thetaBelowCell111133011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011321) h)
        (by
          have h : ((childHL thetaBelowCell111133011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011321) h)
        (by
          have h : ((childHH thetaBelowCell111133011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011321) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011322
        (by
          have h : ((childLL thetaBelowCell111133011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011322) h)
        (by
          have h : ((childLH thetaBelowCell111133011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011322) h)
        (by
          have h : ((childHL thetaBelowCell111133011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011322) h)
        (by
          have h : ((childHH thetaBelowCell111133011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011322) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011323
        (by
          have h : ((childLL thetaBelowCell111133011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011323) h)
        (by
          have h : ((childLH thetaBelowCell111133011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011323) h)
        (by
          have h : ((childHL thetaBelowCell111133011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011323) h)
        (by
          have h : ((childHH thetaBelowCell111133011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011323) h))

theorem cover_subtree_2e2978a517d6 :
    adaptiveCoverCheck 7 (childHH (childHH (childLH thetaBelowCell11113301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH thetaBelowCell11113301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011330
        (by
          have h : ((childLL thetaBelowCell111133011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011330) h)
        (by
          have h : ((childLH thetaBelowCell111133011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011330) h)
        (by
          have h : ((childHL thetaBelowCell111133011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011330) h)
        (by
          have h : ((childHH thetaBelowCell111133011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011331
        (by
          have h : ((childLL thetaBelowCell111133011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011331) h)
        (by
          have h : ((childLH thetaBelowCell111133011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011331) h)
        (by
          have h : ((childHL thetaBelowCell111133011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011331) h)
        (by
          have h : ((childHH thetaBelowCell111133011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011331) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011332
        (by
          have h : ((childLL thetaBelowCell111133011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011332) h)
        (by
          have h : ((childLH thetaBelowCell111133011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011332) h)
        (by
          have h : ((childHL thetaBelowCell111133011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011332) h)
        (by
          have h : ((childHH thetaBelowCell111133011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133011333
        (by
          have h : ((childLL thetaBelowCell111133011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133011333) h)
        (by
          have h : ((childLH thetaBelowCell111133011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133011333) h)
        (by
          have h : ((childHL thetaBelowCell111133011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133011333) h)
        (by
          have h : ((childHH thetaBelowCell111133011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133011333) h))

theorem cover_subtree_f27cd76bf084 :
    adaptiveCoverCheck 8 (childHH (childLH thetaBelowCell11113301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11113301))
    cover_subtree_644ffb1207bc
    cover_subtree_15868ac019bc
    cover_subtree_c4a4ddefa402
    cover_subtree_2e2978a517d6

theorem e24KC2ThetaBelowLeaf111133011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113301)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11113301))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11113301))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11113301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11113301))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11113301))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11113301))) h))
    cover_subtree_c56ac23b21bd
    cover_subtree_f27cd76bf084
theorem e24KC2ThetaBelowLeaf111133012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113301)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL thetaBelowCell11113301))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHL
            thetaBelowCell11113301)))
            (by
              have h : (thetaBelowCell111133012000).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012000 h)
            (by
              have h : (thetaBelowCell111133012001).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012001 h)
            (by
              have h : (thetaBelowCell111133012002).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012002 h)
            (by
              have h : (thetaBelowCell111133012003).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012003 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHL
            thetaBelowCell11113301)))
            (by
              have h : (thetaBelowCell111133012010).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012010 h)
            (by
              have h : (thetaBelowCell111133012011).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012011 h)
            (by
              have h : (thetaBelowCell111133012012).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012012 h)
            (by
              have h : (thetaBelowCell111133012013).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012013 h))
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL
            thetaBelowCell11113301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL thetaBelowCell11113301))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHL
            thetaBelowCell11113301)))
            (by
              have h : (thetaBelowCell111133012100).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012100 h)
            (by
              have h : (thetaBelowCell111133012101).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012101 h)
            (by
              have h : (thetaBelowCell111133012102).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012102 h)
            (by
              have h : (thetaBelowCell111133012103).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012103 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHL
            thetaBelowCell11113301)))
            (by
              have h : (thetaBelowCell111133012110).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012110 h)
            (by
              have h : (thetaBelowCell111133012111).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012111 h)
            (by
              have h : (thetaBelowCell111133012112).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012112 h)
            (by
              have h : (thetaBelowCell111133012113).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133012113 h))
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL
            thetaBelowCell11113301))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell11113301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113301)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113301)) h)
theorem e24KC2ThetaBelowLeaf111133013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113301)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH thetaBelowCell11113301))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHH
            thetaBelowCell11113301)))
            (by
              have h : (thetaBelowCell111133013000).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013000 h)
            (by
              have h : (thetaBelowCell111133013001).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013001 h)
            (by
              have h : (thetaBelowCell111133013002).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013002 h)
            (by
              have h : (thetaBelowCell111133013003).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013003 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHH
            thetaBelowCell11113301)))
            (by
              have h : (thetaBelowCell111133013010).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013010 h)
            (by
              have h : (thetaBelowCell111133013011).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013011 h)
            (by
              have h : (thetaBelowCell111133013012).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013012 h)
            (by
              have h : (thetaBelowCell111133013013).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013013 h))
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH
            thetaBelowCell11113301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH thetaBelowCell11113301))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHH
            thetaBelowCell11113301)))
            (by
              have h : (thetaBelowCell111133013100).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013100 h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133013101
                (by
                  have h : ((childLL thetaBelowCell111133013101)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133013101)
                    h)
                (by
                  have h : ((childLH thetaBelowCell111133013101)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133013101)
                    h)
                (by
                  have h : ((childHL thetaBelowCell111133013101)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133013101)
                    h)
                (by
                  have h : ((childHH thetaBelowCell111133013101)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133013101)
                    h))
            (by
              have h : (thetaBelowCell111133013102).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013102 h)
            (by
              have h : (thetaBelowCell111133013103).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013103 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHH
            thetaBelowCell11113301)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133013110
                (by
                  have h : ((childLL thetaBelowCell111133013110)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133013110)
                    h)
                (by
                  have h : ((childLH thetaBelowCell111133013110)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133013110)
                    h)
                (by
                  have h : ((childHL thetaBelowCell111133013110)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133013110)
                    h)
                (by
                  have h : ((childHH thetaBelowCell111133013110)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133013110)
                    h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133013111
                (by
                  have h : ((childLL thetaBelowCell111133013111)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133013111)
                    h)
                (by
                  have h : ((childLH thetaBelowCell111133013111)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133013111)
                    h)
                (by
                  have h : ((childHL thetaBelowCell111133013111)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133013111)
                    h)
                (by
                  have h : ((childHH thetaBelowCell111133013111)).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133013111)
                    h))
            (by
              have h : (thetaBelowCell111133013112).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013112 h)
            (by
              have h : (thetaBelowCell111133013113).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133013113 h))
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH
            thetaBelowCell11113301))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell11113301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH
            thetaBelowCell11113301))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell11113301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113301)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113301)) h)
theorem cover_subtree_e85bd45b4e1d :
    adaptiveCoverCheck 7 (childLL (childHL (childLL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL thetaBelowCell11113310)))
    (by
      have h : (thetaBelowCell111133100200).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100200 h)
    (by
      have h : (thetaBelowCell111133100201).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100201 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100202
        (by
          have h : ((childLL thetaBelowCell111133100202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100202) h)
        (by
          have h : ((childLH thetaBelowCell111133100202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100202) h)
        (by
          have h : ((childHL thetaBelowCell111133100202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100202) h)
        (by
          have h : ((childHH thetaBelowCell111133100202)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100202) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100203
        (by
          have h : ((childLL thetaBelowCell111133100203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100203) h)
        (by
          have h : ((childLH thetaBelowCell111133100203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100203) h)
        (by
          have h : ((childHL thetaBelowCell111133100203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100203) h)
        (by
          have h : ((childHH thetaBelowCell111133100203)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100203) h))

theorem cover_subtree_0f8d2b9c96c3 :
    adaptiveCoverCheck 7 (childHL (childHL (childLL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100220
        (by
          have h : ((childLL thetaBelowCell111133100220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100220) h)
        (by
          have h : ((childLH thetaBelowCell111133100220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100220) h)
        (by
          have h : ((childHL thetaBelowCell111133100220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100220) h)
        (by
          have h : ((childHH thetaBelowCell111133100220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100220) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100221
        (by
          have h : ((childLL thetaBelowCell111133100221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100221) h)
        (by
          have h : ((childLH thetaBelowCell111133100221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100221) h)
        (by
          have h : ((childHL thetaBelowCell111133100221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100221) h)
        (by
          have h : ((childHH thetaBelowCell111133100221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100221) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100222
        (by
          have h : ((childLL thetaBelowCell111133100222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100222) h)
        (by
          have h : ((childLH thetaBelowCell111133100222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100222) h)
        (by
          have h : ((childHL thetaBelowCell111133100222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100222) h)
        (by
          have h : ((childHH thetaBelowCell111133100222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100223
        (by
          have h : ((childLL thetaBelowCell111133100223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100223) h)
        (by
          have h : ((childLH thetaBelowCell111133100223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100223) h)
        (by
          have h : ((childHL thetaBelowCell111133100223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100223) h)
        (by
          have h : ((childHH thetaBelowCell111133100223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100223) h))

theorem cover_subtree_8e5ba23f7a1f :
    adaptiveCoverCheck 7 (childHH (childHL (childLL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100230
        (by
          have h : ((childLL thetaBelowCell111133100230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100230) h)
        (by
          have h : ((childLH thetaBelowCell111133100230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100230) h)
        (by
          have h : ((childHL thetaBelowCell111133100230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100230) h)
        (by
          have h : ((childHH thetaBelowCell111133100230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100230) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100231
        (by
          have h : ((childLL thetaBelowCell111133100231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100231) h)
        (by
          have h : ((childLH thetaBelowCell111133100231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100231) h)
        (by
          have h : ((childHL thetaBelowCell111133100231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100231) h)
        (by
          have h : ((childHH thetaBelowCell111133100231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100232
        (by
          have h : ((childLL thetaBelowCell111133100232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100232) h)
        (by
          have h : ((childLH thetaBelowCell111133100232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100232) h)
        (by
          have h : ((childHL thetaBelowCell111133100232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100232) h)
        (by
          have h : ((childHH thetaBelowCell111133100232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100233
        (by
          have h : ((childLL thetaBelowCell111133100233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100233) h)
        (by
          have h : ((childLH thetaBelowCell111133100233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100233) h)
        (by
          have h : ((childHL thetaBelowCell111133100233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100233) h)
        (by
          have h : ((childHH thetaBelowCell111133100233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100233) h))

theorem cover_subtree_dfa4585c7b57 :
    adaptiveCoverCheck 8 (childHL (childLL thetaBelowCell11113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11113310))
    cover_subtree_e85bd45b4e1d
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL
        thetaBelowCell11113310)))
        (by
          have h : (thetaBelowCell111133100210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100210 h)
        (by
          have h : (thetaBelowCell111133100211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100211 h)
        (by
          have h : (thetaBelowCell111133100212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100212 h)
        (by
          have h : (thetaBelowCell111133100213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100213 h))
    cover_subtree_0f8d2b9c96c3
    cover_subtree_8e5ba23f7a1f

theorem cover_subtree_c078044ffcf3 :
    adaptiveCoverCheck 6 thetaBelowCell111133100323 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100323
    (by
      have h : ((childLL thetaBelowCell111133100323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100323) h)
    (by
      have h : ((childLH thetaBelowCell111133100323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100323) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133100323)
        (by
          have h : ((childLL (childHL thetaBelowCell111133100323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133100323)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133100323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133100323)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133100323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133100323)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133100323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133100323)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133100323)
        (by
          have h : ((childLL (childHH thetaBelowCell111133100323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133100323)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133100323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133100323)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133100323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133100323)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133100323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133100323)) h))

theorem cover_subtree_4936ea81b96a :
    adaptiveCoverCheck 7 (childHL (childHH (childLL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100320
        (by
          have h : ((childLL thetaBelowCell111133100320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100320) h)
        (by
          have h : ((childLH thetaBelowCell111133100320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100320) h)
        (by
          have h : ((childHL thetaBelowCell111133100320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100320) h)
        (by
          have h : ((childHH thetaBelowCell111133100320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100321
        (by
          have h : ((childLL thetaBelowCell111133100321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100321) h)
        (by
          have h : ((childLH thetaBelowCell111133100321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100321) h)
        (by
          have h : ((childHL thetaBelowCell111133100321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100321) h)
        (by
          have h : ((childHH thetaBelowCell111133100321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100321) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100322
        (by
          have h : ((childLL thetaBelowCell111133100322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100322) h)
        (by
          have h : ((childLH thetaBelowCell111133100322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100322) h)
        (by
          have h : ((childHL thetaBelowCell111133100322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100322) h)
        (by
          have h : ((childHH thetaBelowCell111133100322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100322) h))
    cover_subtree_c078044ffcf3

theorem cover_subtree_4aef0c949cec :
    adaptiveCoverCheck 6 thetaBelowCell111133100332 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100332
    (by
      have h : ((childLL thetaBelowCell111133100332)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100332) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133100332)
        (by
          have h : ((childLL (childLH thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133100332)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133100332)
        (by
          have h : ((childLL (childHL thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133100332)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133100332)
        (by
          have h : ((childLL (childHH thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133100332)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133100332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133100332)) h))

theorem cover_subtree_4d117a1fae58 :
    adaptiveCoverCheck 6 thetaBelowCell111133100333 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100333
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133100333)
        (by
          have h : ((childLL (childLL thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133100333)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133100333)
        (by
          have h : ((childLL (childLH thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133100333)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133100333)
        (by
          have h : ((childLL (childHL thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133100333)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133100333)
        (by
          have h : ((childLL (childHH thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133100333)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133100333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133100333)) h))

theorem cover_subtree_d8cdaaae2631 :
    adaptiveCoverCheck 7 (childHH (childHH (childLL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100330
        (by
          have h : ((childLL thetaBelowCell111133100330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100330) h)
        (by
          have h : ((childLH thetaBelowCell111133100330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100330) h)
        (by
          have h : ((childHL thetaBelowCell111133100330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100330) h)
        (by
          have h : ((childHH thetaBelowCell111133100330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133100330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133100331
        (by
          have h : ((childLL thetaBelowCell111133100331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133100331) h)
        (by
          have h : ((childLH thetaBelowCell111133100331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133100331) h)
        (by
          have h : ((childHL thetaBelowCell111133100331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133100331) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133100331)
            (by
              have h : ((childLL (childHH thetaBelowCell111133100331))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
                thetaBelowCell111133100331)) h)
            (by
              have h : ((childLH (childHH thetaBelowCell111133100331))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
                thetaBelowCell111133100331)) h)
            (by
              have h : ((childHL (childHH thetaBelowCell111133100331))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
                thetaBelowCell111133100331)) h)
            (by
              have h : ((childHH (childHH thetaBelowCell111133100331))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
                thetaBelowCell111133100331)) h)))
    cover_subtree_4aef0c949cec
    cover_subtree_4d117a1fae58

theorem cover_subtree_04c9e6a73353 :
    adaptiveCoverCheck 8 (childHH (childLL thetaBelowCell11113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11113310))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL
        thetaBelowCell11113310)))
        (by
          have h : (thetaBelowCell111133100300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100300 h)
        (by
          have h : (thetaBelowCell111133100301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100301 h)
        (by
          have h : (thetaBelowCell111133100302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100302 h)
        (by
          have h : (thetaBelowCell111133100303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL
        thetaBelowCell11113310)))
        (by
          have h : (thetaBelowCell111133100310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100310 h)
        (by
          have h : (thetaBelowCell111133100311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100311 h)
        (by
          have h : (thetaBelowCell111133100312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100312 h)
        (by
          have h : (thetaBelowCell111133100313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133100313 h))
    cover_subtree_4936ea81b96a
    cover_subtree_d8cdaaae2631

theorem e24KC2ThetaBelowLeaf111133100 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113310)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11113310))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11113310))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11113310))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11113310))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11113310))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11113310))) h))
    cover_subtree_dfa4585c7b57
    cover_subtree_04c9e6a73353
theorem cover_subtree_ac282f2600dc :
    adaptiveCoverCheck 6 thetaBelowCell111133101220 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101220
    (by
      have h : ((childLL thetaBelowCell111133101220)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133101220) h)
    (by
      have h : ((childLH thetaBelowCell111133101220)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133101220) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101220)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101220))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101220)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101220))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101220)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101220))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101220)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101220))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101220)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101220)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101220))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101220)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101220))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101220)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101220))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101220)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101220))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101220)) h))

theorem cover_subtree_073de9109fcf :
    adaptiveCoverCheck 6 thetaBelowCell111133101221 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101221
    (by
      have h : ((childLL thetaBelowCell111133101221)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133101221) h)
    (by
      have h : ((childLH thetaBelowCell111133101221)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133101221) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101221)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101221))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101221)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101221))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101221)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101221))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101221)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101221))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101221)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101221)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101221))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101221)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101221))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101221)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101221))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101221)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101221))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101221)) h))

theorem cover_subtree_09bb9f7fb348 :
    adaptiveCoverCheck 6 thetaBelowCell111133101222 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101222
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133101222)
        (by
          have h : ((childLL (childLL thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133101222)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133101222)
        (by
          have h : ((childLL (childLH thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133101222)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101222)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101222)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101222)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101222)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101222)) h))

theorem cover_subtree_616efb7da0d5 :
    adaptiveCoverCheck 6 thetaBelowCell111133101223 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101223
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133101223)
        (by
          have h : ((childLL (childLL thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133101223)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133101223)
        (by
          have h : ((childLL (childLH thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133101223)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101223)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101223)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101223)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101223)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101223)) h))

theorem cover_subtree_76fb46ac376b :
    adaptiveCoverCheck 7 (childHL (childHL (childLH thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH thetaBelowCell11113310)))
    cover_subtree_ac282f2600dc
    cover_subtree_073de9109fcf
    cover_subtree_09bb9f7fb348
    cover_subtree_616efb7da0d5

theorem cover_subtree_2ee17850d55a :
    adaptiveCoverCheck 6 thetaBelowCell111133101230 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101230
    (by
      have h : ((childLL thetaBelowCell111133101230)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133101230) h)
    (by
      have h : ((childLH thetaBelowCell111133101230)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133101230) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101230)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101230))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101230)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101230))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101230)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101230))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101230)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101230))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101230)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101230)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101230))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101230)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101230))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101230)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101230))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101230)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101230))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101230)) h))

theorem cover_subtree_7a3325b5d632 :
    adaptiveCoverCheck 6 thetaBelowCell111133101232 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101232
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133101232)
        (by
          have h : ((childLL (childLL thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133101232)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133101232)
        (by
          have h : ((childLL (childLH thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133101232)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101232)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101232)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101232)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101232)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101232)) h))

theorem cover_subtree_03b1ead1eef9 :
    adaptiveCoverCheck 6 thetaBelowCell111133101233 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101233
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133101233)
        (by
          have h : ((childLL (childLL thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133101233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133101233)
        (by
          have h : ((childLL (childLH thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133101233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101233)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101233)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101233)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101233)) h))

theorem cover_subtree_3534513f2dea :
    adaptiveCoverCheck 7 (childHH (childHL (childLH thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH thetaBelowCell11113310)))
    cover_subtree_2ee17850d55a
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101231
        (by
          have h : ((childLL thetaBelowCell111133101231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133101231) h)
        (by
          have h : ((childLH thetaBelowCell111133101231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133101231) h)
        (by
          have h : ((childHL thetaBelowCell111133101231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133101231) h)
        (by
          have h : ((childHH thetaBelowCell111133101231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133101231) h))
    cover_subtree_7a3325b5d632
    cover_subtree_03b1ead1eef9

theorem cover_subtree_fee8f6a2356e :
    adaptiveCoverCheck 8 (childHL (childLH thetaBelowCell11113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11113310))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH
        thetaBelowCell11113310)))
        (by
          have h : (thetaBelowCell111133101200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101200 h)
        (by
          have h : (thetaBelowCell111133101201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101201 h)
        (by
          have h : (thetaBelowCell111133101202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101202 h)
        (by
          have h : (thetaBelowCell111133101203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH
        thetaBelowCell11113310)))
        (by
          have h : (thetaBelowCell111133101210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101210 h)
        (by
          have h : (thetaBelowCell111133101211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101211 h)
        (by
          have h : (thetaBelowCell111133101212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101212 h)
        (by
          have h : (thetaBelowCell111133101213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101213 h))
    cover_subtree_76fb46ac376b
    cover_subtree_3534513f2dea

theorem cover_subtree_5721355f2386 :
    adaptiveCoverCheck 6 thetaBelowCell111133101322 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101322
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133101322)
        (by
          have h : ((childLL (childLL thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133101322)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133101322)
        (by
          have h : ((childLL (childLH thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133101322)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101322)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101322)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101322)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101322)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101322)) h))

theorem cover_subtree_c66d1685818d :
    adaptiveCoverCheck 6 thetaBelowCell111133101323 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101323
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133101323)
        (by
          have h : ((childLL (childLL thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133101323)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133101323)
        (by
          have h : ((childLL (childLH thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133101323)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101323)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101323)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101323)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101323)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101323)) h))

theorem cover_subtree_8703d282848e :
    adaptiveCoverCheck 7 (childHL (childHH (childLH thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101320
        (by
          have h : ((childLL thetaBelowCell111133101320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133101320) h)
        (by
          have h : ((childLH thetaBelowCell111133101320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133101320) h)
        (by
          have h : ((childHL thetaBelowCell111133101320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133101320) h)
        (by
          have h : ((childHH thetaBelowCell111133101320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133101320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101321
        (by
          have h : ((childLL thetaBelowCell111133101321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133101321) h)
        (by
          have h : ((childLH thetaBelowCell111133101321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133101321) h)
        (by
          have h : ((childHL thetaBelowCell111133101321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133101321) h)
        (by
          have h : ((childHH thetaBelowCell111133101321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133101321) h))
    cover_subtree_5721355f2386
    cover_subtree_c66d1685818d

theorem cover_subtree_e6b72831ee5a :
    adaptiveCoverCheck 6 thetaBelowCell111133101332 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101332
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133101332)
        (by
          have h : ((childLL (childLL thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133101332)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133101332)
        (by
          have h : ((childLL (childLH thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133101332)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101332)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101332)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101332)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101332)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101332)) h))

theorem cover_subtree_58f9acea628e :
    adaptiveCoverCheck 6 thetaBelowCell111133101333 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101333
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133101333)
        (by
          have h : ((childLL (childLL thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133101333)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133101333)
        (by
          have h : ((childLL (childLH thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133101333)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133101333)
        (by
          have h : ((childLL (childHL thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133101333)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133101333)
        (by
          have h : ((childLL (childHH thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133101333)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133101333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133101333)) h))

theorem cover_subtree_72f2137bba25 :
    adaptiveCoverCheck 7 (childHH (childHH (childLH thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101330
        (by
          have h : ((childLL thetaBelowCell111133101330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133101330) h)
        (by
          have h : ((childLH thetaBelowCell111133101330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133101330) h)
        (by
          have h : ((childHL thetaBelowCell111133101330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133101330) h)
        (by
          have h : ((childHH thetaBelowCell111133101330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133101330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133101331
        (by
          have h : ((childLL thetaBelowCell111133101331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133101331) h)
        (by
          have h : ((childLH thetaBelowCell111133101331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133101331) h)
        (by
          have h : ((childHL thetaBelowCell111133101331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133101331) h)
        (by
          have h : ((childHH thetaBelowCell111133101331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133101331) h))
    cover_subtree_e6b72831ee5a
    cover_subtree_58f9acea628e

theorem cover_subtree_d0cab3230f27 :
    adaptiveCoverCheck 8 (childHH (childLH thetaBelowCell11113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11113310))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH
        thetaBelowCell11113310)))
        (by
          have h : (thetaBelowCell111133101300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101300 h)
        (by
          have h : (thetaBelowCell111133101301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101301 h)
        (by
          have h : (thetaBelowCell111133101302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101302 h)
        (by
          have h : (thetaBelowCell111133101303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH
        thetaBelowCell11113310)))
        (by
          have h : (thetaBelowCell111133101310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101310 h)
        (by
          have h : (thetaBelowCell111133101311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101311 h)
        (by
          have h : (thetaBelowCell111133101312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101312 h)
        (by
          have h : (thetaBelowCell111133101313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133101313 h))
    cover_subtree_8703d282848e
    cover_subtree_72f2137bba25

theorem e24KC2ThetaBelowLeaf111133101 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113310)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11113310))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11113310))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11113310))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11113310))) h))
    cover_subtree_fee8f6a2356e
    cover_subtree_d0cab3230f27
theorem cover_subtree_b25dcd0a7904 :
    adaptiveCoverCheck 7 (childLL (childLL (childHL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHL thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133102000
        (by
          have h : ((childLL thetaBelowCell111133102000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133102000) h)
        (by
          have h : ((childLH thetaBelowCell111133102000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133102000) h)
        (by
          have h : ((childHL thetaBelowCell111133102000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133102000) h)
        (by
          have h : ((childHH thetaBelowCell111133102000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133102000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133102001
        (by
          have h : ((childLL thetaBelowCell111133102001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133102001) h)
        (by
          have h : ((childLH thetaBelowCell111133102001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133102001) h)
        (by
          have h : ((childHL thetaBelowCell111133102001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133102001) h)
        (by
          have h : ((childHH thetaBelowCell111133102001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133102001) h))
    (by
      have h : (thetaBelowCell111133102002).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133102002 h)
    (by
      have h : (thetaBelowCell111133102003).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133102003 h)

theorem cover_subtree_b136e2f967cb :
    adaptiveCoverCheck 7 (childLH (childLL (childHL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHL thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133102010
        (by
          have h : ((childLL thetaBelowCell111133102010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133102010) h)
        (by
          have h : ((childLH thetaBelowCell111133102010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133102010) h)
        (by
          have h : ((childHL thetaBelowCell111133102010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133102010) h)
        (by
          have h : ((childHH thetaBelowCell111133102010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133102010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133102011
        (by
          have h : ((childLL thetaBelowCell111133102011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133102011) h)
        (by
          have h : ((childLH thetaBelowCell111133102011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133102011) h)
        (by
          have h : ((childHL thetaBelowCell111133102011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133102011) h)
        (by
          have h : ((childHH thetaBelowCell111133102011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133102011) h))
    (by
      have h : (thetaBelowCell111133102012).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133102012 h)
    (by
      have h : (thetaBelowCell111133102013).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133102013 h)

theorem cover_subtree_2f872975a74f :
    adaptiveCoverCheck 8 (childLL (childHL thetaBelowCell11113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL thetaBelowCell11113310))
    cover_subtree_b25dcd0a7904
    cover_subtree_b136e2f967cb
    (by
      have h : ((childHL (childLL (childHL thetaBelowCell11113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL
        thetaBelowCell11113310))) h)
    (by
      have h : ((childHH (childLL (childHL thetaBelowCell11113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL
        thetaBelowCell11113310))) h)

theorem cover_subtree_d85bc7893c75 :
    adaptiveCoverCheck 7 (childLL (childLH (childHL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHL thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133102100
        (by
          have h : ((childLL thetaBelowCell111133102100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133102100) h)
        (by
          have h : ((childLH thetaBelowCell111133102100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133102100) h)
        (by
          have h : ((childHL thetaBelowCell111133102100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133102100) h)
        (by
          have h : ((childHH thetaBelowCell111133102100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133102100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133102101
        (by
          have h : ((childLL thetaBelowCell111133102101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133102101) h)
        (by
          have h : ((childLH thetaBelowCell111133102101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133102101) h)
        (by
          have h : ((childHL thetaBelowCell111133102101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133102101) h)
        (by
          have h : ((childHH thetaBelowCell111133102101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133102101) h))
    (by
      have h : (thetaBelowCell111133102102).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133102102 h)
    (by
      have h : (thetaBelowCell111133102103).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133102103 h)

theorem cover_subtree_16d826fbb67f :
    adaptiveCoverCheck 7 (childLH (childLH (childHL thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHL thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133102110
        (by
          have h : ((childLL thetaBelowCell111133102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133102110) h)
        (by
          have h : ((childLH thetaBelowCell111133102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133102110) h)
        (by
          have h : ((childHL thetaBelowCell111133102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133102110) h)
        (by
          have h : ((childHH thetaBelowCell111133102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133102110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133102111
        (by
          have h : ((childLL thetaBelowCell111133102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133102111) h)
        (by
          have h : ((childLH thetaBelowCell111133102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133102111) h)
        (by
          have h : ((childHL thetaBelowCell111133102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133102111) h)
        (by
          have h : ((childHH thetaBelowCell111133102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133102111) h))
    (by
      have h : (thetaBelowCell111133102112).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133102112 h)
    (by
      have h : (thetaBelowCell111133102113).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133102113 h)

theorem cover_subtree_94cd8267c854 :
    adaptiveCoverCheck 8 (childLH (childHL thetaBelowCell11113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL thetaBelowCell11113310))
    cover_subtree_d85bc7893c75
    cover_subtree_16d826fbb67f
    (by
      have h : ((childHL (childLH (childHL thetaBelowCell11113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL
        thetaBelowCell11113310))) h)
    (by
      have h : ((childHH (childLH (childHL thetaBelowCell11113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL
        thetaBelowCell11113310))) h)

theorem e24KC2ThetaBelowLeaf111133102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113310)
    cover_subtree_2f872975a74f
    cover_subtree_94cd8267c854
    (by
      have h : ((childHL (childHL thetaBelowCell11113310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113310)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113310)) h)
theorem cover_subtree_8bd8067ea850 :
    adaptiveCoverCheck 6 thetaBelowCell111133103001 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133103001
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133103001)
        (by
          have h : ((childLL (childLL thetaBelowCell111133103001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133103001)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133103001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133103001)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133103001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133103001)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133103001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133103001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133103001)
        (by
          have h : ((childLL (childLH thetaBelowCell111133103001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133103001)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133103001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133103001)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133103001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133103001)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133103001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133103001)) h))
    (by
      have h : ((childHL thetaBelowCell111133103001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133103001) h)
    (by
      have h : ((childHH thetaBelowCell111133103001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133103001) h)

theorem cover_subtree_e3f60d1c040d :
    adaptiveCoverCheck 7 (childLL (childLL (childHH thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHH thetaBelowCell11113310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133103000
        (by
          have h : ((childLL thetaBelowCell111133103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133103000) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133103000)
            (by
              have h : ((childLL (childLH thetaBelowCell111133103000))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
                thetaBelowCell111133103000)) h)
            (by
              have h : ((childLH (childLH thetaBelowCell111133103000))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
                thetaBelowCell111133103000)) h)
            (by
              have h : ((childHL (childLH thetaBelowCell111133103000))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
                thetaBelowCell111133103000)) h)
            (by
              have h : ((childHH (childLH thetaBelowCell111133103000))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
                thetaBelowCell111133103000)) h))
        (by
          have h : ((childHL thetaBelowCell111133103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133103000) h)
        (by
          have h : ((childHH thetaBelowCell111133103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133103000) h))
    cover_subtree_8bd8067ea850
    (by
      have h : (thetaBelowCell111133103002).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133103002 h)
    (by
      have h : (thetaBelowCell111133103003).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133103003 h)

theorem cover_subtree_542375e93ae0 :
    adaptiveCoverCheck 6 thetaBelowCell111133103010 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133103010
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133103010)
        (by
          have h : ((childLL (childLL thetaBelowCell111133103010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133103010)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133103010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133103010)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133103010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133103010)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133103010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133103010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133103010)
        (by
          have h : ((childLL (childLH thetaBelowCell111133103010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133103010)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133103010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133103010)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133103010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133103010)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133103010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133103010)) h))
    (by
      have h : ((childHL thetaBelowCell111133103010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133103010) h)
    (by
      have h : ((childHH thetaBelowCell111133103010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133103010) h)

theorem cover_subtree_31a24cecd31f :
    adaptiveCoverCheck 6 thetaBelowCell111133103011 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133103011
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133103011)
        (by
          have h : ((childLL (childLL thetaBelowCell111133103011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133103011)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133103011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133103011)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133103011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133103011)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133103011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133103011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133103011)
        (by
          have h : ((childLL (childLH thetaBelowCell111133103011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133103011)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133103011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133103011)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133103011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133103011)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133103011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133103011)) h))
    (by
      have h : ((childHL thetaBelowCell111133103011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133103011) h)
    (by
      have h : ((childHH thetaBelowCell111133103011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133103011) h)

theorem cover_subtree_785b55e573a2 :
    adaptiveCoverCheck 7 (childLH (childLL (childHH thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHH thetaBelowCell11113310)))
    cover_subtree_542375e93ae0
    cover_subtree_31a24cecd31f
    (by
      have h : (thetaBelowCell111133103012).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133103012 h)
    (by
      have h : (thetaBelowCell111133103013).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133103013 h)

theorem cover_subtree_5ea908f6482f :
    adaptiveCoverCheck 8 (childLL (childHH thetaBelowCell11113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH thetaBelowCell11113310))
    cover_subtree_e3f60d1c040d
    cover_subtree_785b55e573a2
    (by
      have h : ((childHL (childLL (childHH thetaBelowCell11113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH
        thetaBelowCell11113310))) h)
    (by
      have h : ((childHH (childLL (childHH thetaBelowCell11113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH
        thetaBelowCell11113310))) h)

theorem cover_subtree_90ee2a55599b :
    adaptiveCoverCheck 6 thetaBelowCell111133103100 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133103100
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133103100)
        (by
          have h : ((childLL (childLL thetaBelowCell111133103100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133103100)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133103100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133103100)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133103100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133103100)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133103100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133103100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133103100)
        (by
          have h : ((childLL (childLH thetaBelowCell111133103100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133103100)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133103100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133103100)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133103100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133103100)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133103100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133103100)) h))
    (by
      have h : ((childHL thetaBelowCell111133103100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133103100) h)
    (by
      have h : ((childHH thetaBelowCell111133103100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133103100) h)

theorem cover_subtree_846f12d54937 :
    adaptiveCoverCheck 6 thetaBelowCell111133103101 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133103101
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133103101)
        (by
          have h : ((childLL (childLL thetaBelowCell111133103101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133103101)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133103101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133103101)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133103101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133103101)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133103101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133103101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133103101)
        (by
          have h : ((childLL (childLH thetaBelowCell111133103101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133103101)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133103101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133103101)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133103101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133103101)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133103101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133103101)) h))
    (by
      have h : ((childHL thetaBelowCell111133103101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133103101) h)
    (by
      have h : ((childHH thetaBelowCell111133103101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133103101) h)

theorem cover_subtree_c6f98b640f2b :
    adaptiveCoverCheck 7 (childLL (childLH (childHH thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHH thetaBelowCell11113310)))
    cover_subtree_90ee2a55599b
    cover_subtree_846f12d54937
    (by
      have h : (thetaBelowCell111133103102).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133103102 h)
    (by
      have h : (thetaBelowCell111133103103).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133103103 h)

theorem cover_subtree_83af3b43e370 :
    adaptiveCoverCheck 6 thetaBelowCell111133103110 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133103110
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133103110)
        (by
          have h : ((childLL (childLL thetaBelowCell111133103110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133103110)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133103110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133103110)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133103110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133103110)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133103110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133103110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133103110)
        (by
          have h : ((childLL (childLH thetaBelowCell111133103110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133103110)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133103110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133103110)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133103110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133103110)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133103110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133103110)) h))
    (by
      have h : ((childHL thetaBelowCell111133103110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133103110) h)
    (by
      have h : ((childHH thetaBelowCell111133103110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133103110) h)

theorem cover_subtree_6c43321af990 :
    adaptiveCoverCheck 6 thetaBelowCell111133103111 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133103111
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133103111)
        (by
          have h : ((childLL (childLL thetaBelowCell111133103111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133103111)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133103111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133103111)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133103111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133103111)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133103111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133103111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133103111)
        (by
          have h : ((childLL (childLH thetaBelowCell111133103111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133103111)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133103111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133103111)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133103111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133103111)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133103111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133103111)) h))
    (by
      have h : ((childHL thetaBelowCell111133103111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133103111) h)
    (by
      have h : ((childHH thetaBelowCell111133103111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133103111) h)

theorem cover_subtree_ad23d1ccf385 :
    adaptiveCoverCheck 7 (childLH (childLH (childHH thetaBelowCell11113310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHH thetaBelowCell11113310)))
    cover_subtree_83af3b43e370
    cover_subtree_6c43321af990
    (by
      have h : (thetaBelowCell111133103112).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133103112 h)
    (by
      have h : (thetaBelowCell111133103113).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133103113 h)

theorem cover_subtree_5edd590faea9 :
    adaptiveCoverCheck 8 (childLH (childHH thetaBelowCell11113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH thetaBelowCell11113310))
    cover_subtree_c6f98b640f2b
    cover_subtree_ad23d1ccf385
    (by
      have h : ((childHL (childLH (childHH thetaBelowCell11113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH
        thetaBelowCell11113310))) h)
    (by
      have h : ((childHH (childLH (childHH thetaBelowCell11113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH
        thetaBelowCell11113310))) h)

theorem e24KC2ThetaBelowLeaf111133103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113310)
    cover_subtree_5ea908f6482f
    cover_subtree_5edd590faea9
    (by
      have h : ((childHL (childHH thetaBelowCell11113310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113310)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH thetaBelowCell11113310))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH
            thetaBelowCell11113310))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell11113310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH
            thetaBelowCell11113310))) h))

end PartE
end GerverSofa

end

end

end
