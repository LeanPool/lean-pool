/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT716800017`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2af6f575e7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1120 : AngleCell :=
  childLL (childHL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1121 : AngleCell :=
  childLH (childHL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1122 : AngleCell :=
  childHL (childHL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1123 : AngleCell :=
  childHH (childHL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1130 : AngleCell :=
  childLL (childHH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1131 : AngleCell :=
  childLH (childHH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1132 : AngleCell :=
  childHL (childHH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1133 : AngleCell :=
  childHH (childHH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1300 : AngleCell :=
  childLL (childLL (childHH (childLH e24ThetaBelowRoot)))
/-- Subcell `1301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1301 : AngleCell :=
  childLH (childLL (childHH (childLH e24ThetaBelowRoot)))
/-- Subcell `1302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1302 : AngleCell :=
  childHL (childLL (childHH (childLH e24ThetaBelowRoot)))
/-- Subcell `1303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1303 : AngleCell :=
  childHH (childLL (childHH (childLH e24ThetaBelowRoot)))
/-- Subcell `1310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1310 : AngleCell :=
  childLL (childLH (childHH (childLH e24ThetaBelowRoot)))
/-- Subcell `1311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1311 : AngleCell :=
  childLH (childLH (childHH (childLH e24ThetaBelowRoot)))
/-- Subcell `1312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1312 : AngleCell :=
  childHL (childLH (childHH (childLH e24ThetaBelowRoot)))
/-- Subcell `1313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1313 : AngleCell :=
  childHH (childLH (childHH (childLH e24ThetaBelowRoot)))
/-- Subcell `11103020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11112000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11113020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaBelowCell1111)))

end CertificateCells2af6f575e7

open CertificateCells2af6f575e7
theorem e24KC2ThetaBelowLeaf111030203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103020) = true := by
  have h : ((childHH thetaBelowCell11103020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103020) h
theorem e24KC2ThetaBelowLeaf111030210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103021) = true := by
  have h : ((childLL thetaBelowCell11103021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103021) h
theorem e24KC2ThetaBelowLeaf111030211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103021) = true := by
  have h : ((childLH thetaBelowCell11103021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103021) h
theorem e24KC2ThetaBelowLeaf111030212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103021) = true := by
  have h : ((childHL thetaBelowCell11103021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103021) h
theorem e24KC2ThetaBelowLeaf111030213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103021) = true := by
  have h : ((childHH thetaBelowCell11103021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103021) h
theorem e24KC2ThetaBelowLeaf111030220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103022) = true := by
  have h : ((childLL thetaBelowCell11103022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103022) h
theorem e24KC2ThetaBelowLeaf111030221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103022) = true := by
  have h : ((childLH thetaBelowCell11103022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103022) h
theorem e24KC2ThetaBelowLeaf111030222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103022) = true := by
  have h : ((childHL thetaBelowCell11103022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103022) h
theorem e24KC2ThetaBelowLeaf111030230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103023) = true := by
  have h : ((childLL thetaBelowCell11103023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103023) h
theorem e24KC2ThetaBelowLeaf111030231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103023) = true := by
  have h : ((childLH thetaBelowCell11103023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103023) h
theorem e24KC2ThetaBelowLeaf111030300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103030) = true := by
  have h : ((childLL thetaBelowCell11103030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103030) h
theorem e24KC2ThetaBelowLeaf111030301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103030) = true := by
  have h : ((childLH thetaBelowCell11103030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103030) h
theorem e24KC2ThetaBelowLeaf111030302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103030) = true := by
  have h : ((childHL thetaBelowCell11103030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103030) h
theorem e24KC2ThetaBelowLeaf111030303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103030) = true := by
  have h : ((childHH thetaBelowCell11103030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103030) h
theorem e24KC2ThetaBelowLeaf111030310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103031) = true := by
  have h : ((childLL thetaBelowCell11103031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103031) h
theorem e24KC2ThetaBelowLeaf111030311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103031) = true := by
  have h : ((childLH thetaBelowCell11103031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103031) h
theorem e24KC2ThetaBelowLeaf11103100 :
    adaptiveCoverCheck 10 thetaBelowCell11103100 = true := by
  have h : (thetaBelowCell11103100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103100 h
theorem e24KC2ThetaBelowLeaf11103101 :
    adaptiveCoverCheck 10 thetaBelowCell11103101 = true := by
  have h : (thetaBelowCell11103101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103101 h
theorem e24KC2ThetaBelowLeaf11103102 :
    adaptiveCoverCheck 10 thetaBelowCell11103102 = true := by
  have h : (thetaBelowCell11103102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103102 h
theorem e24KC2ThetaBelowLeaf11103103 :
    adaptiveCoverCheck 10 thetaBelowCell11103103 = true := by
  have h : (thetaBelowCell11103103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103103 h
theorem e24KC2ThetaBelowLeaf11103110 :
    adaptiveCoverCheck 10 thetaBelowCell11103110 = true := by
  have h : (thetaBelowCell11103110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103110 h
theorem e24KC2ThetaBelowLeaf11103111 :
    adaptiveCoverCheck 10 thetaBelowCell11103111 = true := by
  have h : (thetaBelowCell11103111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103111 h
theorem e24KC2ThetaBelowLeaf11103112 :
    adaptiveCoverCheck 10 thetaBelowCell11103112 = true := by
  have h : (thetaBelowCell11103112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103112 h
theorem e24KC2ThetaBelowLeaf11103113 :
    adaptiveCoverCheck 10 thetaBelowCell11103113 = true := by
  have h : (thetaBelowCell11103113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103113 h
theorem e24KC2ThetaBelowLeaf111031200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103120) = true := by
  have h : ((childLL thetaBelowCell11103120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103120) h
theorem e24KC2ThetaBelowLeaf111031201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103120) = true := by
  have h : ((childLH thetaBelowCell11103120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103120) h
theorem e24KC2ThetaBelowLeaf111031203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103120) = true := by
  have h : ((childHH thetaBelowCell11103120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103120) h
theorem e24KC2ThetaBelowLeaf111031210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103121) = true := by
  have h : ((childLL thetaBelowCell11103121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103121) h
theorem e24KC2ThetaBelowLeaf111031211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103121) = true := by
  have h : ((childLH thetaBelowCell11103121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103121) h
theorem e24KC2ThetaBelowLeaf111031212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103121) = true := by
  have h : ((childHL thetaBelowCell11103121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103121) h
theorem e24KC2ThetaBelowLeaf111031213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103121) = true := by
  have h : ((childHH thetaBelowCell11103121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103121) h
theorem e24KC2ThetaBelowLeaf111031300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103130) = true := by
  have h : ((childLL thetaBelowCell11103130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103130) h
theorem e24KC2ThetaBelowLeaf111031301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103130) = true := by
  have h : ((childLH thetaBelowCell11103130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103130) h
theorem e24KC2ThetaBelowLeaf111031302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103130) = true := by
  have h : ((childHL thetaBelowCell11103130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103130) h
theorem e24KC2ThetaBelowLeaf111031303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103130) = true := by
  have h : ((childHH thetaBelowCell11103130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103130) h
theorem e24KC2ThetaBelowLeaf111031310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103131) = true := by
  have h : ((childLL thetaBelowCell11103131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103131) h
theorem e24KC2ThetaBelowLeaf111031311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103131) = true := by
  have h : ((childLH thetaBelowCell11103131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103131) h
theorem e24KC2ThetaBelowLeaf111031312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103131) = true := by
  have h : ((childHL thetaBelowCell11103131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103131) h
theorem e24KC2ThetaBelowLeaf111031313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103131) = true := by
  have h : ((childHH thetaBelowCell11103131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103131) h
theorem e24KC2ThetaBelowLeaf111032000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103200) = true := by
  have h : ((childLL thetaBelowCell11103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103200) h
theorem e24KC2ThetaBelowLeaf111032001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103200) = true := by
  have h : ((childLH thetaBelowCell11103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103200) h
theorem e24KC2ThetaBelowLeaf111032002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103200) = true := by
  have h : ((childHL thetaBelowCell11103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103200) h
theorem e24KC2ThetaBelowLeaf111032003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103200) = true := by
  have h : ((childHH thetaBelowCell11103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103200) h
theorem e24KC2ThetaBelowLeaf111032010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103201) = true := by
  have h : ((childLL thetaBelowCell11103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103201) h
theorem e24KC2ThetaBelowLeaf111032011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103201) = true := by
  have h : ((childLH thetaBelowCell11103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103201) h
theorem e24KC2ThetaBelowLeaf111032012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103201) = true := by
  have h : ((childHL thetaBelowCell11103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103201) h
theorem e24KC2ThetaBelowLeaf111032013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103201) = true := by
  have h : ((childHH thetaBelowCell11103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103201) h
theorem e24KC2ThetaBelowLeaf11103202 :
    adaptiveCoverCheck 10 thetaBelowCell11103202 = true := by
  have h : (thetaBelowCell11103202).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103202 h
theorem e24KC2ThetaBelowLeaf11103203 :
    adaptiveCoverCheck 10 thetaBelowCell11103203 = true := by
  have h : (thetaBelowCell11103203).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103203 h
theorem e24KC2ThetaBelowLeaf111032102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103210) = true := by
  have h : ((childHL thetaBelowCell11103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103210) h
theorem e24KC2ThetaBelowLeaf111032103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103210) = true := by
  have h : ((childHH thetaBelowCell11103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103210) h
theorem e24KC2ThetaBelowLeaf111032112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103211) = true := by
  have h : ((childHL thetaBelowCell11103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103211) h
theorem e24KC2ThetaBelowLeaf111032113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103211) = true := by
  have h : ((childHH thetaBelowCell11103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103211) h
theorem e24KC2ThetaBelowLeaf11103212 :
    adaptiveCoverCheck 10 thetaBelowCell11103212 = true := by
  have h : (thetaBelowCell11103212).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103212 h
theorem e24KC2ThetaBelowLeaf11103213 :
    adaptiveCoverCheck 10 thetaBelowCell11103213 = true := by
  have h : (thetaBelowCell11103213).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103213 h
theorem e24KC2ThetaBelowLeaf1110322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1110))) = true := by
  have h : ((childHL (childHL (childHH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1110))) = true := by
  have h : ((childHH (childHL (childHH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf111033002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103300) = true := by
  have h : ((childHL thetaBelowCell11103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103300) h
theorem e24KC2ThetaBelowLeaf111033003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103300) = true := by
  have h : ((childHH thetaBelowCell11103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103300) h
theorem e24KC2ThetaBelowLeaf111033012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103301) = true := by
  have h : ((childHL thetaBelowCell11103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103301) h
theorem e24KC2ThetaBelowLeaf111033013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103301) = true := by
  have h : ((childHH thetaBelowCell11103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103301) h
theorem e24KC2ThetaBelowLeaf11103302 :
    adaptiveCoverCheck 10 thetaBelowCell11103302 = true := by
  have h : (thetaBelowCell11103302).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103302 h
theorem e24KC2ThetaBelowLeaf11103303 :
    adaptiveCoverCheck 10 thetaBelowCell11103303 = true := by
  have h : (thetaBelowCell11103303).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103303 h
theorem e24KC2ThetaBelowLeaf111033102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103310) = true := by
  have h : ((childHL thetaBelowCell11103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103310) h
theorem e24KC2ThetaBelowLeaf111033103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103310) = true := by
  have h : ((childHH thetaBelowCell11103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103310) h
theorem e24KC2ThetaBelowLeaf111033112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103311) = true := by
  have h : ((childHL thetaBelowCell11103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103311) h
theorem e24KC2ThetaBelowLeaf111033113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103311) = true := by
  have h : ((childHH thetaBelowCell11103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103311) h
theorem e24KC2ThetaBelowLeaf11103312 :
    adaptiveCoverCheck 10 thetaBelowCell11103312 = true := by
  have h : (thetaBelowCell11103312).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103312 h
theorem e24KC2ThetaBelowLeaf11103313 :
    adaptiveCoverCheck 10 thetaBelowCell11103313 = true := by
  have h : (thetaBelowCell11103313).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103313 h
theorem e24KC2ThetaBelowLeaf1110332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1110))) = true := by
  have h : ((childHL (childHH (childHH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1110))) = true := by
  have h : ((childHH (childHH (childHH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf111100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1111)) = true := by
  have h : ((childLL (childLL thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf111101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1111)) = true := by
  have h : ((childLH (childLL thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf1111020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1111))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1111))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1111))) = true := by
  have h : ((childHL (childHL (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1111))) = true := by
  have h : ((childHH (childHL (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1111))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1111))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1111))) = true := by
  have h : ((childHL (childHH (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1111))) = true := by
  have h : ((childHH (childHH (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf111110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1111)) = true := by
  have h : ((childLL (childLH thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf111111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1111)) = true := by
  have h : ((childLH (childLH thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf1111120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1111))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1111))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1111))) = true := by
  have h : ((childHL (childHL (childLH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1111))) = true := by
  have h : ((childHH (childHL (childLH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf111113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1111)) = true := by
  have h : ((childHH (childLH thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf11112000 :
    adaptiveCoverCheck 10 thetaBelowCell11112000 = true := by
  have h : (thetaBelowCell11112000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112000 h
theorem e24KC2ThetaBelowLeaf11112001 :
    adaptiveCoverCheck 10 thetaBelowCell11112001 = true := by
  have h : (thetaBelowCell11112001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112001 h
theorem e24KC2ThetaBelowLeaf11112002 :
    adaptiveCoverCheck 10 thetaBelowCell11112002 = true := by
  have h : (thetaBelowCell11112002).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112002 h
theorem e24KC2ThetaBelowLeaf11112003 :
    adaptiveCoverCheck 10 thetaBelowCell11112003 = true := by
  have h : (thetaBelowCell11112003).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112003 h
theorem e24KC2ThetaBelowLeaf11112010 :
    adaptiveCoverCheck 10 thetaBelowCell11112010 = true := by
  have h : (thetaBelowCell11112010).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112010 h
theorem e24KC2ThetaBelowLeaf11112011 :
    adaptiveCoverCheck 10 thetaBelowCell11112011 = true := by
  have h : (thetaBelowCell11112011).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112011 h
theorem e24KC2ThetaBelowLeaf11112012 :
    adaptiveCoverCheck 10 thetaBelowCell11112012 = true := by
  have h : (thetaBelowCell11112012).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112012 h
theorem e24KC2ThetaBelowLeaf11112013 :
    adaptiveCoverCheck 10 thetaBelowCell11112013 = true := by
  have h : (thetaBelowCell11112013).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112013 h
theorem e24KC2ThetaBelowLeaf111120200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112020) = true := by
  have h : ((childLL thetaBelowCell11112020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112020) h
theorem e24KC2ThetaBelowLeaf111120201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112020) = true := by
  have h : ((childLH thetaBelowCell11112020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112020) h
theorem e24KC2ThetaBelowLeaf111120202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112020) = true := by
  have h : ((childHL thetaBelowCell11112020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112020) h
theorem e24KC2ThetaBelowLeaf111120203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112020) = true := by
  have h : ((childHH thetaBelowCell11112020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112020) h
theorem e24KC2ThetaBelowLeaf111120210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112021) = true := by
  have h : ((childLL thetaBelowCell11112021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112021) h
theorem e24KC2ThetaBelowLeaf111120211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112021) = true := by
  have h : ((childLH thetaBelowCell11112021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112021) h
theorem e24KC2ThetaBelowLeaf111120212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112021) = true := by
  have h : ((childHL thetaBelowCell11112021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112021) h
theorem e24KC2ThetaBelowLeaf111120213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112021) = true := by
  have h : ((childHH thetaBelowCell11112021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112021) h
theorem e24KC2ThetaBelowLeaf111120300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112030) = true := by
  have h : ((childLL thetaBelowCell11112030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112030) h
theorem e24KC2ThetaBelowLeaf111120301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112030) = true := by
  have h : ((childLH thetaBelowCell11112030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112030) h
theorem e24KC2ThetaBelowLeaf111120302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112030) = true := by
  have h : ((childHL thetaBelowCell11112030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112030) h
theorem e24KC2ThetaBelowLeaf111120303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112030) = true := by
  have h : ((childHH thetaBelowCell11112030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112030) h
theorem e24KC2ThetaBelowLeaf111120310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112031) = true := by
  have h : ((childLL thetaBelowCell11112031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112031) h
theorem e24KC2ThetaBelowLeaf111120311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112031) = true := by
  have h : ((childLH thetaBelowCell11112031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112031) h
theorem e24KC2ThetaBelowLeaf111120312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112031) = true := by
  have h : ((childHL thetaBelowCell11112031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112031) h
theorem e24KC2ThetaBelowLeaf111120313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112031) = true := by
  have h : ((childHH thetaBelowCell11112031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112031) h
theorem e24KC2ThetaBelowLeaf11112100 :
    adaptiveCoverCheck 10 thetaBelowCell11112100 = true := by
  have h : (thetaBelowCell11112100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112100 h
theorem e24KC2ThetaBelowLeaf11112101 :
    adaptiveCoverCheck 10 thetaBelowCell11112101 = true := by
  have h : (thetaBelowCell11112101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112101 h
theorem e24KC2ThetaBelowLeaf11112102 :
    adaptiveCoverCheck 10 thetaBelowCell11112102 = true := by
  have h : (thetaBelowCell11112102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112102 h
theorem e24KC2ThetaBelowLeaf11112103 :
    adaptiveCoverCheck 10 thetaBelowCell11112103 = true := by
  have h : (thetaBelowCell11112103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112103 h
theorem e24KC2ThetaBelowLeaf11112110 :
    adaptiveCoverCheck 10 thetaBelowCell11112110 = true := by
  have h : (thetaBelowCell11112110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112110 h
theorem e24KC2ThetaBelowLeaf11112111 :
    adaptiveCoverCheck 10 thetaBelowCell11112111 = true := by
  have h : (thetaBelowCell11112111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112111 h
theorem e24KC2ThetaBelowLeaf11112112 :
    adaptiveCoverCheck 10 thetaBelowCell11112112 = true := by
  have h : (thetaBelowCell11112112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112112 h
theorem e24KC2ThetaBelowLeaf11112113 :
    adaptiveCoverCheck 10 thetaBelowCell11112113 = true := by
  have h : (thetaBelowCell11112113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112113 h
theorem e24KC2ThetaBelowLeaf111121200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112120) = true := by
  have h : ((childLL thetaBelowCell11112120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112120) h
theorem e24KC2ThetaBelowLeaf111121201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112120) = true := by
  have h : ((childLH thetaBelowCell11112120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112120) h
theorem e24KC2ThetaBelowLeaf111121202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112120) = true := by
  have h : ((childHL thetaBelowCell11112120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112120) h
theorem e24KC2ThetaBelowLeaf111121203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112120) = true := by
  have h : ((childHH thetaBelowCell11112120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112120) h
theorem e24KC2ThetaBelowLeaf111121210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112121) = true := by
  have h : ((childLL thetaBelowCell11112121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112121) h
theorem e24KC2ThetaBelowLeaf111121211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112121) = true := by
  have h : ((childLH thetaBelowCell11112121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112121) h
theorem e24KC2ThetaBelowLeaf111121212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112121) = true := by
  have h : ((childHL thetaBelowCell11112121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112121) h
theorem e24KC2ThetaBelowLeaf111121213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112121) = true := by
  have h : ((childHH thetaBelowCell11112121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112121) h
theorem e24KC2ThetaBelowLeaf111121300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112130) = true := by
  have h : ((childLL thetaBelowCell11112130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112130) h
theorem e24KC2ThetaBelowLeaf111121301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112130) = true := by
  have h : ((childLH thetaBelowCell11112130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112130) h
theorem e24KC2ThetaBelowLeaf111121302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112130) = true := by
  have h : ((childHL thetaBelowCell11112130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112130) h
theorem e24KC2ThetaBelowLeaf111121303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112130) = true := by
  have h : ((childHH thetaBelowCell11112130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112130) h
theorem e24KC2ThetaBelowLeaf11112131 :
    adaptiveCoverCheck 10 thetaBelowCell11112131 = true := by
  have h : (thetaBelowCell11112131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112131 h
theorem e24KC2ThetaBelowLeaf111121320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112132) = true := by
  have h : ((childLL thetaBelowCell11112132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112132) h
theorem e24KC2ThetaBelowLeaf111121321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112132) = true := by
  have h : ((childLH thetaBelowCell11112132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112132) h
theorem e24KC2ThetaBelowLeaf111121330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112133) = true := by
  have h : ((childLL thetaBelowCell11112133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112133) h
theorem e24KC2ThetaBelowLeaf111121331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112133) = true := by
  have h : ((childLH thetaBelowCell11112133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112133) h
theorem e24KC2ThetaBelowLeaf111122002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112200) = true := by
  have h : ((childHL thetaBelowCell11112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112200) h
theorem e24KC2ThetaBelowLeaf111122003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112200) = true := by
  have h : ((childHH thetaBelowCell11112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112200) h
theorem e24KC2ThetaBelowLeaf111122012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112201) = true := by
  have h : ((childHL thetaBelowCell11112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112201) h
theorem e24KC2ThetaBelowLeaf111122013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112201) = true := by
  have h : ((childHH thetaBelowCell11112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112201) h
theorem e24KC2ThetaBelowLeaf11112202 :
    adaptiveCoverCheck 10 thetaBelowCell11112202 = true := by
  have h : (thetaBelowCell11112202).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112202 h
theorem e24KC2ThetaBelowLeaf11112203 :
    adaptiveCoverCheck 10 thetaBelowCell11112203 = true := by
  have h : (thetaBelowCell11112203).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112203 h
theorem e24KC2ThetaBelowLeaf111122102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112210) = true := by
  have h : ((childHL thetaBelowCell11112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112210) h
theorem e24KC2ThetaBelowLeaf111122103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112210) = true := by
  have h : ((childHH thetaBelowCell11112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112210) h
theorem e24KC2ThetaBelowLeaf111122112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112211) = true := by
  have h : ((childHL thetaBelowCell11112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112211) h
theorem e24KC2ThetaBelowLeaf111122120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112212) = true := by
  have h : ((childLL thetaBelowCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112212) h
theorem e24KC2ThetaBelowLeaf111122121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112212) = true := by
  have h : ((childLH thetaBelowCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112212) h
theorem e24KC2ThetaBelowLeaf111122122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112212) = true := by
  have h : ((childHL thetaBelowCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112212) h
theorem e24KC2ThetaBelowLeaf111122123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112212) = true := by
  have h : ((childHH thetaBelowCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112212) h
theorem e24KC2ThetaBelowLeaf111122130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112213) = true := by
  have h : ((childLL thetaBelowCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112213) h
theorem e24KC2ThetaBelowLeaf111122131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112213) = true := by
  have h : ((childLH thetaBelowCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112213) h
theorem e24KC2ThetaBelowLeaf111122132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112213) = true := by
  have h : ((childHL thetaBelowCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112213) h
theorem e24KC2ThetaBelowLeaf111122133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112213) = true := by
  have h : ((childHH thetaBelowCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112213) h
theorem e24KC2ThetaBelowLeaf11112220 :
    adaptiveCoverCheck 10 thetaBelowCell11112220 = true := by
  have h : (thetaBelowCell11112220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112220 h
theorem e24KC2ThetaBelowLeaf11112221 :
    adaptiveCoverCheck 10 thetaBelowCell11112221 = true := by
  have h : (thetaBelowCell11112221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112221 h
theorem e24KC2ThetaBelowLeaf11112222 :
    adaptiveCoverCheck 10 thetaBelowCell11112222 = true := by
  have h : (thetaBelowCell11112222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112222 h
theorem e24KC2ThetaBelowLeaf11112223 :
    adaptiveCoverCheck 10 thetaBelowCell11112223 = true := by
  have h : (thetaBelowCell11112223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112223 h
theorem e24KC2ThetaBelowLeaf11112230 :
    adaptiveCoverCheck 10 thetaBelowCell11112230 = true := by
  have h : (thetaBelowCell11112230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112230 h
theorem e24KC2ThetaBelowLeaf11112231 :
    adaptiveCoverCheck 10 thetaBelowCell11112231 = true := by
  have h : (thetaBelowCell11112231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112231 h
theorem e24KC2ThetaBelowLeaf11112232 :
    adaptiveCoverCheck 10 thetaBelowCell11112232 = true := by
  have h : (thetaBelowCell11112232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112232 h
theorem e24KC2ThetaBelowLeaf11112233 :
    adaptiveCoverCheck 10 thetaBelowCell11112233 = true := by
  have h : (thetaBelowCell11112233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112233 h
theorem e24KC2ThetaBelowLeaf111123020 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112302) = true := by
  have h : ((childLL thetaBelowCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112302) h
theorem e24KC2ThetaBelowLeaf111123021 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112302) = true := by
  have h : ((childLH thetaBelowCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112302) h
theorem e24KC2ThetaBelowLeaf111123022 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112302) = true := by
  have h : ((childHL thetaBelowCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112302) h
theorem e24KC2ThetaBelowLeaf111123023 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112302) = true := by
  have h : ((childHH thetaBelowCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112302) h
theorem e24KC2ThetaBelowLeaf111123030 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112303) = true := by
  have h : ((childLL thetaBelowCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112303) h
theorem e24KC2ThetaBelowLeaf111123031 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112303) = true := by
  have h : ((childLH thetaBelowCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112303) h
theorem e24KC2ThetaBelowLeaf111123032 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112303) = true := by
  have h : ((childHL thetaBelowCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112303) h
theorem e24KC2ThetaBelowLeaf111123033 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112303) = true := by
  have h : ((childHH thetaBelowCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112303) h
theorem e24KC2ThetaBelowLeaf111123120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112312) = true := by
  have h : ((childLL thetaBelowCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112312) h
theorem e24KC2ThetaBelowLeaf111123121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112312) = true := by
  have h : ((childLH thetaBelowCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112312) h
theorem e24KC2ThetaBelowLeaf111123122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112312) = true := by
  have h : ((childHL thetaBelowCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112312) h
theorem e24KC2ThetaBelowLeaf111123123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112312) = true := by
  have h : ((childHH thetaBelowCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112312) h
theorem e24KC2ThetaBelowLeaf111123130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112313) = true := by
  have h : ((childLL thetaBelowCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112313) h
theorem e24KC2ThetaBelowLeaf111123131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112313) = true := by
  have h : ((childLH thetaBelowCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112313) h
theorem e24KC2ThetaBelowLeaf111123132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112313) = true := by
  have h : ((childHL thetaBelowCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112313) h
theorem e24KC2ThetaBelowLeaf111123133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112313) = true := by
  have h : ((childHH thetaBelowCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112313) h
theorem e24KC2ThetaBelowLeaf11112320 :
    adaptiveCoverCheck 10 thetaBelowCell11112320 = true := by
  have h : (thetaBelowCell11112320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112320 h
theorem e24KC2ThetaBelowLeaf11112321 :
    adaptiveCoverCheck 10 thetaBelowCell11112321 = true := by
  have h : (thetaBelowCell11112321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112321 h
theorem e24KC2ThetaBelowLeaf11112322 :
    adaptiveCoverCheck 10 thetaBelowCell11112322 = true := by
  have h : (thetaBelowCell11112322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112322 h
theorem e24KC2ThetaBelowLeaf11112323 :
    adaptiveCoverCheck 10 thetaBelowCell11112323 = true := by
  have h : (thetaBelowCell11112323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112323 h
theorem e24KC2ThetaBelowLeaf11112330 :
    adaptiveCoverCheck 10 thetaBelowCell11112330 = true := by
  have h : (thetaBelowCell11112330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112330 h
theorem e24KC2ThetaBelowLeaf11112331 :
    adaptiveCoverCheck 10 thetaBelowCell11112331 = true := by
  have h : (thetaBelowCell11112331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112331 h
theorem e24KC2ThetaBelowLeaf11112332 :
    adaptiveCoverCheck 10 thetaBelowCell11112332 = true := by
  have h : (thetaBelowCell11112332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112332 h
theorem e24KC2ThetaBelowLeaf11112333 :
    adaptiveCoverCheck 10 thetaBelowCell11112333 = true := by
  have h : (thetaBelowCell11112333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112333 h
theorem e24KC2ThetaBelowLeaf1111300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1111))) = true := by
  have h : ((childLL (childLL (childHH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1111))) = true := by
  have h : ((childLH (childLL (childHH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf11113020 :
    adaptiveCoverCheck 10 thetaBelowCell11113020 = true := by
  have h : (thetaBelowCell11113020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113020 h
theorem e24KC2ThetaBelowLeaf11113021 :
    adaptiveCoverCheck 10 thetaBelowCell11113021 = true := by
  have h : (thetaBelowCell11113021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113021 h
theorem e24KC2ThetaBelowLeaf111130220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113022) = true := by
  have h : ((childLL thetaBelowCell11113022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113022) h
theorem e24KC2ThetaBelowLeaf111130221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113022) = true := by
  have h : ((childLH thetaBelowCell11113022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113022) h
theorem e24KC2ThetaBelowLeaf111130230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113023) = true := by
  have h : ((childLL thetaBelowCell11113023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113023) h
theorem e24KC2ThetaBelowLeaf111130231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113023) = true := by
  have h : ((childLH thetaBelowCell11113023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113023) h
theorem e24KC2ThetaBelowLeaf11113030 :
    adaptiveCoverCheck 10 thetaBelowCell11113030 = true := by
  have h : (thetaBelowCell11113030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113030 h
theorem e24KC2ThetaBelowLeaf11113031 :
    adaptiveCoverCheck 10 thetaBelowCell11113031 = true := by
  have h : (thetaBelowCell11113031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113031 h
theorem e24KC2ThetaBelowLeaf111130320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113032) = true := by
  have h : ((childLL thetaBelowCell11113032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113032) h
theorem e24KC2ThetaBelowLeaf111130321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113032) = true := by
  have h : ((childLH thetaBelowCell11113032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113032) h
theorem e24KC2ThetaBelowLeaf111130330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113033) = true := by
  have h : ((childLL thetaBelowCell11113033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113033) h
theorem e24KC2ThetaBelowLeaf111130331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113033) = true := by
  have h : ((childLH thetaBelowCell11113033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113033) h
theorem e24KC2ThetaBelowLeaf1111310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1111))) = true := by
  have h : ((childLL (childLH (childHH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1111))) = true := by
  have h : ((childLH (childLH (childHH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf11113120 :
    adaptiveCoverCheck 10 thetaBelowCell11113120 = true := by
  have h : (thetaBelowCell11113120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113120 h
theorem e24KC2ThetaBelowLeaf11113121 :
    adaptiveCoverCheck 10 thetaBelowCell11113121 = true := by
  have h : (thetaBelowCell11113121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113121 h
theorem e24KC2ThetaBelowLeaf111131220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113122) = true := by
  have h : ((childLL thetaBelowCell11113122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113122) h
theorem e24KC2ThetaBelowLeaf111131221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113122) = true := by
  have h : ((childLH thetaBelowCell11113122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113122) h
theorem e24KC2ThetaBelowLeaf111131230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113123) = true := by
  have h : ((childLL thetaBelowCell11113123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113123) h
theorem e24KC2ThetaBelowLeaf111131231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113123) = true := by
  have h : ((childLH thetaBelowCell11113123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113123) h
theorem e24KC2ThetaBelowLeaf11113130 :
    adaptiveCoverCheck 10 thetaBelowCell11113130 = true := by
  have h : (thetaBelowCell11113130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113130 h
theorem e24KC2ThetaBelowLeaf11113131 :
    adaptiveCoverCheck 10 thetaBelowCell11113131 = true := by
  have h : (thetaBelowCell11113131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113131 h
theorem e24KC2ThetaBelowLeaf111131320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113132) = true := by
  have h : ((childLL thetaBelowCell11113132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113132) h
theorem e24KC2ThetaBelowLeaf111131321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113132) = true := by
  have h : ((childLH thetaBelowCell11113132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113132) h
theorem e24KC2ThetaBelowLeaf111131330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113133) = true := by
  have h : ((childLL thetaBelowCell11113133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113133) h
theorem e24KC2ThetaBelowLeaf111131331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113133) = true := by
  have h : ((childLH thetaBelowCell11113133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113133) h
theorem e24KC2ThetaBelowLeaf111132020 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113202) = true := by
  have h : ((childLL thetaBelowCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113202) h
theorem e24KC2ThetaBelowLeaf111132021 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113202) = true := by
  have h : ((childLH thetaBelowCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113202) h
theorem e24KC2ThetaBelowLeaf111132022 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113202) = true := by
  have h : ((childHL thetaBelowCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113202) h
theorem e24KC2ThetaBelowLeaf111132023 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113202) = true := by
  have h : ((childHH thetaBelowCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113202) h
theorem e24KC2ThetaBelowLeaf111132030 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113203) = true := by
  have h : ((childLL thetaBelowCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113203) h
theorem e24KC2ThetaBelowLeaf111132031 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113203) = true := by
  have h : ((childLH thetaBelowCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113203) h
theorem e24KC2ThetaBelowLeaf111132032 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113203) = true := by
  have h : ((childHL thetaBelowCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113203) h
theorem e24KC2ThetaBelowLeaf111132033 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113203) = true := by
  have h : ((childHH thetaBelowCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113203) h
theorem e24KC2ThetaBelowLeaf111132120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113212) = true := by
  have h : ((childLL thetaBelowCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113212) h
theorem e24KC2ThetaBelowLeaf111132121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113212) = true := by
  have h : ((childLH thetaBelowCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113212) h
theorem e24KC2ThetaBelowLeaf111132122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113212) = true := by
  have h : ((childHL thetaBelowCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113212) h
theorem e24KC2ThetaBelowLeaf111132123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113212) = true := by
  have h : ((childHH thetaBelowCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113212) h
theorem e24KC2ThetaBelowLeaf111132130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113213) = true := by
  have h : ((childLL thetaBelowCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113213) h
theorem e24KC2ThetaBelowLeaf111132131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113213) = true := by
  have h : ((childLH thetaBelowCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113213) h
theorem e24KC2ThetaBelowLeaf111132132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113213) = true := by
  have h : ((childHL thetaBelowCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113213) h
theorem e24KC2ThetaBelowLeaf111132133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113213) = true := by
  have h : ((childHH thetaBelowCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113213) h
theorem e24KC2ThetaBelowLeaf11113220 :
    adaptiveCoverCheck 10 thetaBelowCell11113220 = true := by
  have h : (thetaBelowCell11113220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113220 h
theorem e24KC2ThetaBelowLeaf11113221 :
    adaptiveCoverCheck 10 thetaBelowCell11113221 = true := by
  have h : (thetaBelowCell11113221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113221 h
theorem e24KC2ThetaBelowLeaf11113222 :
    adaptiveCoverCheck 10 thetaBelowCell11113222 = true := by
  have h : (thetaBelowCell11113222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113222 h
theorem e24KC2ThetaBelowLeaf11113223 :
    adaptiveCoverCheck 10 thetaBelowCell11113223 = true := by
  have h : (thetaBelowCell11113223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113223 h
theorem e24KC2ThetaBelowLeaf11113230 :
    adaptiveCoverCheck 10 thetaBelowCell11113230 = true := by
  have h : (thetaBelowCell11113230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113230 h
theorem e24KC2ThetaBelowLeaf11113231 :
    adaptiveCoverCheck 10 thetaBelowCell11113231 = true := by
  have h : (thetaBelowCell11113231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113231 h
theorem e24KC2ThetaBelowLeaf11113232 :
    adaptiveCoverCheck 10 thetaBelowCell11113232 = true := by
  have h : (thetaBelowCell11113232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113232 h
theorem e24KC2ThetaBelowLeaf11113233 :
    adaptiveCoverCheck 10 thetaBelowCell11113233 = true := by
  have h : (thetaBelowCell11113233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113233 h
theorem e24KC2ThetaBelowLeaf111133020 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113302) = true := by
  have h : ((childLL thetaBelowCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113302) h
theorem e24KC2ThetaBelowLeaf111133021 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113302) = true := by
  have h : ((childLH thetaBelowCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113302) h
theorem e24KC2ThetaBelowLeaf111133022 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113302) = true := by
  have h : ((childHL thetaBelowCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113302) h
theorem e24KC2ThetaBelowLeaf111133023 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113302) = true := by
  have h : ((childHH thetaBelowCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113302) h
theorem e24KC2ThetaBelowLeaf111133030 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113303) = true := by
  have h : ((childLL thetaBelowCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113303) h
theorem e24KC2ThetaBelowLeaf111133031 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113303) = true := by
  have h : ((childLH thetaBelowCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113303) h
theorem e24KC2ThetaBelowLeaf111133032 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113303) = true := by
  have h : ((childHL thetaBelowCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113303) h
theorem e24KC2ThetaBelowLeaf111133033 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113303) = true := by
  have h : ((childHH thetaBelowCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113303) h
theorem e24KC2ThetaBelowLeaf111133122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113312) = true := by
  have h : ((childHL thetaBelowCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113312) h
theorem e24KC2ThetaBelowLeaf111133123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113312) = true := by
  have h : ((childHH thetaBelowCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113312) h
theorem e24KC2ThetaBelowLeaf111133132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113313) = true := by
  have h : ((childHL thetaBelowCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113313) h
theorem e24KC2ThetaBelowLeaf111133133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113313) = true := by
  have h : ((childHH thetaBelowCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113313) h
theorem e24KC2ThetaBelowLeaf11113320 :
    adaptiveCoverCheck 10 thetaBelowCell11113320 = true := by
  have h : (thetaBelowCell11113320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113320 h
theorem e24KC2ThetaBelowLeaf11113321 :
    adaptiveCoverCheck 10 thetaBelowCell11113321 = true := by
  have h : (thetaBelowCell11113321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113321 h
theorem e24KC2ThetaBelowLeaf11113322 :
    adaptiveCoverCheck 10 thetaBelowCell11113322 = true := by
  have h : (thetaBelowCell11113322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113322 h
theorem e24KC2ThetaBelowLeaf11113323 :
    adaptiveCoverCheck 10 thetaBelowCell11113323 = true := by
  have h : (thetaBelowCell11113323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113323 h
theorem e24KC2ThetaBelowLeaf11113330 :
    adaptiveCoverCheck 10 thetaBelowCell11113330 = true := by
  have h : (thetaBelowCell11113330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113330 h
theorem e24KC2ThetaBelowLeaf11113331 :
    adaptiveCoverCheck 10 thetaBelowCell11113331 = true := by
  have h : (thetaBelowCell11113331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113331 h
theorem e24KC2ThetaBelowLeaf11113332 :
    adaptiveCoverCheck 10 thetaBelowCell11113332 = true := by
  have h : (thetaBelowCell11113332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113332 h
theorem e24KC2ThetaBelowLeaf11113333 :
    adaptiveCoverCheck 10 thetaBelowCell11113333 = true := by
  have h : (thetaBelowCell11113333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113333 h
theorem e24KC2ThetaBelowLeaf111200 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1112)) = true := by
  have h : ((childLL (childLL thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf111201 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1112)) = true := by
  have h : ((childLH (childLL thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf111202 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1112)) = true := by
  have h : ((childHL (childLL thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf111203 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1112)) = true := by
  have h : ((childHH (childLL thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf1112100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH thetaBelowCell1112))) = true := by
  have h : ((childLL (childLL (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH thetaBelowCell1112))) = true := by
  have h : ((childLH (childLL (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH thetaBelowCell1112))) = true := by
  have h : ((childHL (childLL (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH thetaBelowCell1112))) = true := by
  have h : ((childHH (childLL (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH thetaBelowCell1112))) = true := by
  have h : ((childLL (childLH (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH thetaBelowCell1112))) = true := by
  have h : ((childLH (childLH (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH thetaBelowCell1112))) = true := by
  have h : ((childHL (childLH (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH thetaBelowCell1112))) = true := by
  have h : ((childHH (childLH (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf111212 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1112)) = true := by
  have h : ((childHL (childLH thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf111213 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1112)) = true := by
  have h : ((childHH (childLH thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf11122 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1112) = true := by
  have h : ((childHL thetaBelowCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1112) h
theorem e24KC2ThetaBelowLeaf11123 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1112) = true := by
  have h : ((childHH thetaBelowCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1112) h
theorem e24KC2ThetaBelowLeaf1113000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL thetaBelowCell1113))) = true := by
  have h : ((childLL (childLL (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL thetaBelowCell1113))) = true := by
  have h : ((childLH (childLL (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL thetaBelowCell1113))) = true := by
  have h : ((childHL (childLL (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL thetaBelowCell1113))) = true := by
  have h : ((childHH (childLL (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL thetaBelowCell1113))) = true := by
  have h : ((childLL (childLH (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL thetaBelowCell1113))) = true := by
  have h : ((childLH (childLH (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL thetaBelowCell1113))) = true := by
  have h : ((childHL (childLH (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL thetaBelowCell1113))) = true := by
  have h : ((childHH (childLH (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf111302 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1113)) = true := by
  have h : ((childHL (childLL thetaBelowCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1113)) h
theorem e24KC2ThetaBelowLeaf111303 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1113)) = true := by
  have h : ((childHH (childLL thetaBelowCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1113)) h
theorem e24KC2ThetaBelowLeaf1113100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH thetaBelowCell1113))) = true := by
  have h : ((childLL (childLL (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH thetaBelowCell1113))) = true := by
  have h : ((childLH (childLL (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH thetaBelowCell1113))) = true := by
  have h : ((childHL (childLL (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH thetaBelowCell1113))) = true := by
  have h : ((childHH (childLL (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH thetaBelowCell1113))) = true := by
  have h : ((childLL (childLH (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH thetaBelowCell1113))) = true := by
  have h : ((childLH (childLH (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH thetaBelowCell1113))) = true := by
  have h : ((childHL (childLH (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH thetaBelowCell1113))) = true := by
  have h : ((childHH (childLH (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf111312 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1113)) = true := by
  have h : ((childHL (childLH thetaBelowCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1113)) h
theorem e24KC2ThetaBelowLeaf111313 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1113)) = true := by
  have h : ((childHH (childLH thetaBelowCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1113)) h
theorem e24KC2ThetaBelowLeaf11132 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1113) = true := by
  have h : ((childHL thetaBelowCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1113) h
theorem e24KC2ThetaBelowLeaf11133 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1113) = true := by
  have h : ((childHH thetaBelowCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1113) h
theorem e24KC2ThetaBelowLeaf1120 :
    adaptiveCoverCheck 14 thetaBelowCell1120 = true := by
  have h : (thetaBelowCell1120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1120 h
theorem e24KC2ThetaBelowLeaf11210 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1121) = true := by
  have h : ((childLL thetaBelowCell1121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1121) h
theorem e24KC2ThetaBelowLeaf11211 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1121) = true := by
  have h : ((childLH thetaBelowCell1121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell1121) h
theorem e24KC2ThetaBelowLeaf11212 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1121) = true := by
  have h : ((childHL thetaBelowCell1121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1121) h
theorem e24KC2ThetaBelowLeaf11213 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1121) = true := by
  have h : ((childHH thetaBelowCell1121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1121) h
theorem e24KC2ThetaBelowLeaf1122 :
    adaptiveCoverCheck 14 thetaBelowCell1122 = true := by
  have h : (thetaBelowCell1122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1122 h
theorem e24KC2ThetaBelowLeaf1123 :
    adaptiveCoverCheck 14 thetaBelowCell1123 = true := by
  have h : (thetaBelowCell1123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1123 h
theorem e24KC2ThetaBelowLeaf11300 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1130) = true := by
  have h : ((childLL thetaBelowCell1130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1130) h
theorem e24KC2ThetaBelowLeaf11301 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1130) = true := by
  have h : ((childLH thetaBelowCell1130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell1130) h
theorem e24KC2ThetaBelowLeaf11302 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1130) = true := by
  have h : ((childHL thetaBelowCell1130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1130) h
theorem e24KC2ThetaBelowLeaf11303 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1130) = true := by
  have h : ((childHH thetaBelowCell1130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1130) h
theorem e24KC2ThetaBelowLeaf11310 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1131) = true := by
  have h : ((childLL thetaBelowCell1131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1131) h
theorem e24KC2ThetaBelowLeaf11311 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1131) = true := by
  have h : ((childLH thetaBelowCell1131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell1131) h
theorem e24KC2ThetaBelowLeaf11312 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1131) = true := by
  have h : ((childHL thetaBelowCell1131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1131) h
theorem e24KC2ThetaBelowLeaf11313 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1131) = true := by
  have h : ((childHH thetaBelowCell1131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1131) h
theorem e24KC2ThetaBelowLeaf1132 :
    adaptiveCoverCheck 14 thetaBelowCell1132 = true := by
  have h : (thetaBelowCell1132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1132 h
theorem e24KC2ThetaBelowLeaf1133 :
    adaptiveCoverCheck 14 thetaBelowCell1133 = true := by
  have h : (thetaBelowCell1133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1133 h
theorem e24KC2ThetaBelowLeaf120 :
    adaptiveCoverCheck 15 (childLL (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHL (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf121 :
    adaptiveCoverCheck 15 (childLH (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHL (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf122 :
    adaptiveCoverCheck 15 (childHL (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHL (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf123 :
    adaptiveCoverCheck 15 (childHH (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHL (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf1300 :
    adaptiveCoverCheck 14 thetaBelowCell1300 = true := by
  have h : (thetaBelowCell1300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1300 h
theorem e24KC2ThetaBelowLeaf1301 :
    adaptiveCoverCheck 14 thetaBelowCell1301 = true := by
  have h : (thetaBelowCell1301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1301 h
theorem e24KC2ThetaBelowLeaf1302 :
    adaptiveCoverCheck 14 thetaBelowCell1302 = true := by
  have h : (thetaBelowCell1302).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1302 h
theorem e24KC2ThetaBelowLeaf1303 :
    adaptiveCoverCheck 14 thetaBelowCell1303 = true := by
  have h : (thetaBelowCell1303).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1303 h
theorem e24KC2ThetaBelowLeaf1310 :
    adaptiveCoverCheck 14 thetaBelowCell1310 = true := by
  have h : (thetaBelowCell1310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1310 h
theorem e24KC2ThetaBelowLeaf1311 :
    adaptiveCoverCheck 14 thetaBelowCell1311 = true := by
  have h : (thetaBelowCell1311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1311 h
theorem e24KC2ThetaBelowLeaf1312 :
    adaptiveCoverCheck 14 thetaBelowCell1312 = true := by
  have h : (thetaBelowCell1312).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1312 h
theorem e24KC2ThetaBelowLeaf1313 :
    adaptiveCoverCheck 14 thetaBelowCell1313 = true := by
  have h : (thetaBelowCell1313).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1313 h
theorem e24KC2ThetaBelowLeaf132 :
    adaptiveCoverCheck 15 (childHL (childHH (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childHH (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHH (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf133 :
    adaptiveCoverCheck 15 (childHH (childHH (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHH (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf2 :
    adaptiveCoverCheck 17 (childHL e24ThetaBelowRoot) = true := by
  have h : physicallyIrrelevant (childHL e24ThetaBelowRoot) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 17 (childHL e24ThetaBelowRoot) h
theorem e24KC2ThetaBelowLeaf300 :
    adaptiveCoverCheck 15 (childLL (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childLL (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf301 :
    adaptiveCoverCheck 15 (childLH (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childLL (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf302 :
    adaptiveCoverCheck 15 (childHL (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childLL (childHH
    e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf303 :
    adaptiveCoverCheck 15 (childHH (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childLL (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf310 :
    adaptiveCoverCheck 15 (childLL (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childLH (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf311 :
    adaptiveCoverCheck 15 (childLH (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childLH (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf312 :
    adaptiveCoverCheck 15 (childHL (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childLH (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf313 :
    adaptiveCoverCheck 15 (childHH (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childLH (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf32 :
    adaptiveCoverCheck 16 (childHL (childHH e24ThetaBelowRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childHH e24ThetaBelowRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childHH e24ThetaBelowRoot)) h

theorem e24KC2ThetaBelowLeaf330 :
    adaptiveCoverCheck 15 (childLL (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childLL (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childLL (childHH (childHH
    e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf331 :
    adaptiveCoverCheck 15 (childLH (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf332 :
    adaptiveCoverCheck 15 (childHL (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childHH (childHH
    e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf333 :
    adaptiveCoverCheck 15 (childHH (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHH (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHH (childHH (childHH
    e24ThetaBelowRoot))) h

end PartE
end GerverSofa

end

end

end
