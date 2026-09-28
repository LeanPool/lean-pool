/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT614400015`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2f4f8ea4fc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1120 : AngleCell :=
  childLL (childHL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1121 : AngleCell :=
  childLH (childHL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1122 : AngleCell :=
  childHL (childHL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1123 : AngleCell :=
  childHH (childHL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1130 : AngleCell :=
  childLL (childHH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1131 : AngleCell :=
  childLH (childHH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1132 : AngleCell :=
  childHL (childHH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `1133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1133 : AngleCell :=
  childHH (childHH (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `0000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0002 : AngleCell :=
  childHL (childLL (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0003 : AngleCell :=
  childHH (childLL (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0012 : AngleCell :=
  childHL (childLH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0013 : AngleCell :=
  childHH (childLH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0030 : AngleCell :=
  childLL (childHH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0031 : AngleCell :=
  childLH (childHH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0032 : AngleCell :=
  childHL (childHH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0033 : AngleCell :=
  childHH (childHH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0102 : AngleCell :=
  childHL (childLL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0103 : AngleCell :=
  childHH (childLL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0112 : AngleCell :=
  childHL (childLH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0113 : AngleCell :=
  childHH (childLH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0120 : AngleCell :=
  childLL (childHL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0121 : AngleCell :=
  childLH (childHL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0122 : AngleCell :=
  childHL (childHL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0123 : AngleCell :=
  childHH (childHL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0130 : AngleCell :=
  childLL (childHH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0131 : AngleCell :=
  childLH (childHH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0132 : AngleCell :=
  childHL (childHH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0133 : AngleCell :=
  childHH (childHH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `1000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1002 : AngleCell :=
  childHL (childLL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1003 : AngleCell :=
  childHH (childLL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1011 : AngleCell :=
  childLH (childLH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1012 : AngleCell :=
  childHL (childLH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1013 : AngleCell :=
  childHH (childLH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1020 : AngleCell :=
  childLL (childHL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1021 : AngleCell :=
  childLH (childHL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1022 : AngleCell :=
  childHL (childHL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `11112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11112333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1111)))
/-- Subcell `11113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1111)))
/-- Subcell `11113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1111)))
/-- Subcell `11113333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1111)))
/-- Subcell `10113030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1011)))
/-- Subcell `10113031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1011)))
/-- Subcell `10113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1011)))
/-- Subcell `10113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1011)))
/-- Subcell `10113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1011)))
/-- Subcell `10113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1011)))

end CertificateCells2f4f8ea4fc

open CertificateCells2f4f8ea4fc
theorem e24KC2ThetaAboveLeaf111123311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112331) = true := by
  have h : ((childLH thetaAboveCell11112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112331) h
theorem e24KC2ThetaAboveLeaf111123312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112331) = true := by
  have h : ((childHL thetaAboveCell11112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112331) h
theorem e24KC2ThetaAboveLeaf111123313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112331) = true := by
  have h : ((childHH thetaAboveCell11112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112331) h
theorem e24KC2ThetaAboveLeaf111123320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112332) = true := by
  have h : ((childLL thetaAboveCell11112332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112332) h
theorem e24KC2ThetaAboveLeaf111123321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112332) = true := by
  have h : ((childLH thetaAboveCell11112332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112332) h
theorem e24KC2ThetaAboveLeaf111123322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112332) = true := by
  have h : ((childHL thetaAboveCell11112332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112332) h
theorem e24KC2ThetaAboveLeaf111123323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112332) = true := by
  have h : ((childHH thetaAboveCell11112332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112332) h
theorem e24KC2ThetaAboveLeaf111123330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112333) = true := by
  have h : ((childLL thetaAboveCell11112333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112333) h
theorem e24KC2ThetaAboveLeaf111123331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112333) = true := by
  have h : ((childLH thetaAboveCell11112333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112333) h
theorem e24KC2ThetaAboveLeaf111123332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112333) = true := by
  have h : ((childHL thetaAboveCell11112333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112333) h
theorem e24KC2ThetaAboveLeaf111123333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112333) = true := by
  have h : ((childHH thetaAboveCell11112333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112333) h
theorem e24KC2ThetaAboveLeaf1111300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1111))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1111))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1111))) = true := by
  have h : ((childHL (childLL (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1111))) = true := by
  have h : ((childHH (childLL (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1111))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1111))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1111))) = true := by
  have h : ((childHL (childLH (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1111))) = true := by
  have h : ((childHH (childLH (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf11113200 :
    adaptiveCoverCheck 11 thetaAboveCell11113200 = true := by
  have h : (thetaAboveCell11113200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113200 h
theorem e24KC2ThetaAboveLeaf11113201 :
    adaptiveCoverCheck 11 thetaAboveCell11113201 = true := by
  have h : (thetaAboveCell11113201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113201 h
theorem e24KC2ThetaAboveLeaf111132020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113202) = true := by
  have h : ((childLL thetaAboveCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113202) h
theorem e24KC2ThetaAboveLeaf111132021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113202) = true := by
  have h : ((childLH thetaAboveCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113202) h
theorem e24KC2ThetaAboveLeaf111132022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113202) = true := by
  have h : ((childHL thetaAboveCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113202) h
theorem e24KC2ThetaAboveLeaf111132023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113202) = true := by
  have h : ((childHH thetaAboveCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113202) h
theorem e24KC2ThetaAboveLeaf111132030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113203) = true := by
  have h : ((childLL thetaAboveCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113203) h
theorem e24KC2ThetaAboveLeaf111132031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113203) = true := by
  have h : ((childLH thetaAboveCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113203) h
theorem e24KC2ThetaAboveLeaf111132032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113203) = true := by
  have h : ((childHL thetaAboveCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113203) h
theorem e24KC2ThetaAboveLeaf111132033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113203) = true := by
  have h : ((childHH thetaAboveCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113203) h
theorem e24KC2ThetaAboveLeaf11113210 :
    adaptiveCoverCheck 11 thetaAboveCell11113210 = true := by
  have h : (thetaAboveCell11113210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113210 h
theorem e24KC2ThetaAboveLeaf11113211 :
    adaptiveCoverCheck 11 thetaAboveCell11113211 = true := by
  have h : (thetaAboveCell11113211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113211 h
theorem e24KC2ThetaAboveLeaf111132120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113212) = true := by
  have h : ((childLL thetaAboveCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113212) h
theorem e24KC2ThetaAboveLeaf111132121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113212) = true := by
  have h : ((childLH thetaAboveCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113212) h
theorem e24KC2ThetaAboveLeaf111132122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113212) = true := by
  have h : ((childHL thetaAboveCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113212) h
theorem e24KC2ThetaAboveLeaf111132123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113212) = true := by
  have h : ((childHH thetaAboveCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113212) h
theorem e24KC2ThetaAboveLeaf111132130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113213) = true := by
  have h : ((childLL thetaAboveCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113213) h
theorem e24KC2ThetaAboveLeaf111132131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113213) = true := by
  have h : ((childLH thetaAboveCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113213) h
theorem e24KC2ThetaAboveLeaf111132132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113213) = true := by
  have h : ((childHL thetaAboveCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113213) h
theorem e24KC2ThetaAboveLeaf111132133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113213) = true := by
  have h : ((childHH thetaAboveCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113213) h
theorem e24KC2ThetaAboveLeaf111132200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113220) = true := by
  have h : ((childLL thetaAboveCell11113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113220) h
theorem e24KC2ThetaAboveLeaf111132201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113220) = true := by
  have h : ((childLH thetaAboveCell11113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113220) h
theorem e24KC2ThetaAboveLeaf111132202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113220) = true := by
  have h : ((childHL thetaAboveCell11113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113220) h
theorem e24KC2ThetaAboveLeaf111132203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113220) = true := by
  have h : ((childHH thetaAboveCell11113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113220) h
theorem e24KC2ThetaAboveLeaf111132210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113221) = true := by
  have h : ((childLL thetaAboveCell11113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113221) h
theorem e24KC2ThetaAboveLeaf111132211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113221) = true := by
  have h : ((childLH thetaAboveCell11113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113221) h
theorem e24KC2ThetaAboveLeaf111132212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113221) = true := by
  have h : ((childHL thetaAboveCell11113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113221) h
theorem e24KC2ThetaAboveLeaf111132213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113221) = true := by
  have h : ((childHH thetaAboveCell11113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113221) h
theorem e24KC2ThetaAboveLeaf111132220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113222) = true := by
  have h : ((childLL thetaAboveCell11113222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113222) h
theorem e24KC2ThetaAboveLeaf111132221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113222) = true := by
  have h : ((childLH thetaAboveCell11113222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113222) h
theorem e24KC2ThetaAboveLeaf111132222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113222) = true := by
  have h : ((childHL thetaAboveCell11113222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113222) h
theorem e24KC2ThetaAboveLeaf111132223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113222) = true := by
  have h : ((childHH thetaAboveCell11113222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113222) h
theorem e24KC2ThetaAboveLeaf111132230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113223) = true := by
  have h : ((childLL thetaAboveCell11113223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113223) h
theorem e24KC2ThetaAboveLeaf111132231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113223) = true := by
  have h : ((childLH thetaAboveCell11113223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113223) h
theorem e24KC2ThetaAboveLeaf111132232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113223) = true := by
  have h : ((childHL thetaAboveCell11113223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113223) h
theorem e24KC2ThetaAboveLeaf111132233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113223) = true := by
  have h : ((childHH thetaAboveCell11113223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113223) h
theorem e24KC2ThetaAboveLeaf111132300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113230) = true := by
  have h : ((childLL thetaAboveCell11113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113230) h
theorem e24KC2ThetaAboveLeaf111132301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113230) = true := by
  have h : ((childLH thetaAboveCell11113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113230) h
theorem e24KC2ThetaAboveLeaf111132302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113230) = true := by
  have h : ((childHL thetaAboveCell11113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113230) h
theorem e24KC2ThetaAboveLeaf111132303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113230) = true := by
  have h : ((childHH thetaAboveCell11113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113230) h
theorem e24KC2ThetaAboveLeaf111132310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113231) = true := by
  have h : ((childLL thetaAboveCell11113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113231) h
theorem e24KC2ThetaAboveLeaf111132311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113231) = true := by
  have h : ((childLH thetaAboveCell11113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113231) h
theorem e24KC2ThetaAboveLeaf111132312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113231) = true := by
  have h : ((childHL thetaAboveCell11113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113231) h
theorem e24KC2ThetaAboveLeaf111132313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113231) = true := by
  have h : ((childHH thetaAboveCell11113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113231) h
theorem e24KC2ThetaAboveLeaf111132320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113232) = true := by
  have h : ((childLL thetaAboveCell11113232)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113232) h
theorem e24KC2ThetaAboveLeaf111132321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113232) = true := by
  have h : ((childLH thetaAboveCell11113232)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113232) h
theorem e24KC2ThetaAboveLeaf111132322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113232) = true := by
  have h : ((childHL thetaAboveCell11113232)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113232) h
theorem e24KC2ThetaAboveLeaf111132323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113232) = true := by
  have h : ((childHH thetaAboveCell11113232)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113232) h
theorem e24KC2ThetaAboveLeaf111132330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113233) = true := by
  have h : ((childLL thetaAboveCell11113233)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113233) h
theorem e24KC2ThetaAboveLeaf111132331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113233) = true := by
  have h : ((childLH thetaAboveCell11113233)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113233) h
theorem e24KC2ThetaAboveLeaf111132332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113233) = true := by
  have h : ((childHL thetaAboveCell11113233)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113233) h
theorem e24KC2ThetaAboveLeaf111132333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113233) = true := by
  have h : ((childHH thetaAboveCell11113233)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113233) h
theorem e24KC2ThetaAboveLeaf11113300 :
    adaptiveCoverCheck 11 thetaAboveCell11113300 = true := by
  have h : (thetaAboveCell11113300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113300 h
theorem e24KC2ThetaAboveLeaf11113301 :
    adaptiveCoverCheck 11 thetaAboveCell11113301 = true := by
  have h : (thetaAboveCell11113301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113301 h
theorem e24KC2ThetaAboveLeaf111133020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113302) = true := by
  have h : ((childLL thetaAboveCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113302) h
theorem e24KC2ThetaAboveLeaf111133021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113302) = true := by
  have h : ((childLH thetaAboveCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113302) h
theorem e24KC2ThetaAboveLeaf111133022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113302) = true := by
  have h : ((childHL thetaAboveCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113302) h
theorem e24KC2ThetaAboveLeaf111133023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113302) = true := by
  have h : ((childHH thetaAboveCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113302) h
theorem e24KC2ThetaAboveLeaf111133030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113303) = true := by
  have h : ((childLL thetaAboveCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113303) h
theorem e24KC2ThetaAboveLeaf111133031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113303) = true := by
  have h : ((childLH thetaAboveCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113303) h
theorem e24KC2ThetaAboveLeaf111133032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113303) = true := by
  have h : ((childHL thetaAboveCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113303) h
theorem e24KC2ThetaAboveLeaf111133033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113303) = true := by
  have h : ((childHH thetaAboveCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113303) h
theorem e24KC2ThetaAboveLeaf11113310 :
    adaptiveCoverCheck 11 thetaAboveCell11113310 = true := by
  have h : (thetaAboveCell11113310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113310 h
theorem e24KC2ThetaAboveLeaf11113311 :
    adaptiveCoverCheck 11 thetaAboveCell11113311 = true := by
  have h : (thetaAboveCell11113311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113311 h
theorem e24KC2ThetaAboveLeaf111133120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113312) = true := by
  have h : ((childLL thetaAboveCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113312) h
theorem e24KC2ThetaAboveLeaf111133121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113312) = true := by
  have h : ((childLH thetaAboveCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113312) h
theorem e24KC2ThetaAboveLeaf111133122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113312) = true := by
  have h : ((childHL thetaAboveCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113312) h
theorem e24KC2ThetaAboveLeaf111133123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113312) = true := by
  have h : ((childHH thetaAboveCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113312) h
theorem e24KC2ThetaAboveLeaf111133130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113313) = true := by
  have h : ((childLL thetaAboveCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113313) h
theorem e24KC2ThetaAboveLeaf111133131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113313) = true := by
  have h : ((childLH thetaAboveCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113313) h
theorem e24KC2ThetaAboveLeaf111133132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113313) = true := by
  have h : ((childHL thetaAboveCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113313) h
theorem e24KC2ThetaAboveLeaf111133133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113313) = true := by
  have h : ((childHH thetaAboveCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113313) h
theorem e24KC2ThetaAboveLeaf111133200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113320) = true := by
  have h : ((childLL thetaAboveCell11113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113320) h
theorem e24KC2ThetaAboveLeaf111133201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113320) = true := by
  have h : ((childLH thetaAboveCell11113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113320) h
theorem e24KC2ThetaAboveLeaf111133202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113320) = true := by
  have h : ((childHL thetaAboveCell11113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113320) h
theorem e24KC2ThetaAboveLeaf111133203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113320) = true := by
  have h : ((childHH thetaAboveCell11113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113320) h
theorem e24KC2ThetaAboveLeaf111133210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113321) = true := by
  have h : ((childLL thetaAboveCell11113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113321) h
theorem e24KC2ThetaAboveLeaf111133211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113321) = true := by
  have h : ((childLH thetaAboveCell11113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113321) h
theorem e24KC2ThetaAboveLeaf111133212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113321) = true := by
  have h : ((childHL thetaAboveCell11113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113321) h
theorem e24KC2ThetaAboveLeaf111133213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113321) = true := by
  have h : ((childHH thetaAboveCell11113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113321) h
theorem e24KC2ThetaAboveLeaf111133220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113322) = true := by
  have h : ((childLL thetaAboveCell11113322)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113322) h
theorem e24KC2ThetaAboveLeaf111133221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113322) = true := by
  have h : ((childLH thetaAboveCell11113322)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113322) h
theorem e24KC2ThetaAboveLeaf111133222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113322) = true := by
  have h : ((childHL thetaAboveCell11113322)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113322) h
theorem e24KC2ThetaAboveLeaf111133223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113322) = true := by
  have h : ((childHH thetaAboveCell11113322)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113322) h
theorem e24KC2ThetaAboveLeaf111133230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113323) = true := by
  have h : ((childLL thetaAboveCell11113323)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113323) h
theorem e24KC2ThetaAboveLeaf111133231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113323) = true := by
  have h : ((childLH thetaAboveCell11113323)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113323) h
theorem e24KC2ThetaAboveLeaf111133232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113323) = true := by
  have h : ((childHL thetaAboveCell11113323)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113323) h
theorem e24KC2ThetaAboveLeaf111133233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113323) = true := by
  have h : ((childHH thetaAboveCell11113323)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113323) h
theorem e24KC2ThetaAboveLeaf111133300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113330) = true := by
  have h : ((childLL thetaAboveCell11113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113330) h
theorem e24KC2ThetaAboveLeaf111133301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113330) = true := by
  have h : ((childLH thetaAboveCell11113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113330) h
theorem e24KC2ThetaAboveLeaf111133302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113330) = true := by
  have h : ((childHL thetaAboveCell11113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113330) h
theorem e24KC2ThetaAboveLeaf111133303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113330) = true := by
  have h : ((childHH thetaAboveCell11113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113330) h
theorem e24KC2ThetaAboveLeaf111133310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113331) = true := by
  have h : ((childLL thetaAboveCell11113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113331) h
theorem e24KC2ThetaAboveLeaf111133311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113331) = true := by
  have h : ((childLH thetaAboveCell11113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113331) h
theorem e24KC2ThetaAboveLeaf111133312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113331) = true := by
  have h : ((childHL thetaAboveCell11113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113331) h
theorem e24KC2ThetaAboveLeaf111133313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113331) = true := by
  have h : ((childHH thetaAboveCell11113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113331) h
theorem e24KC2ThetaAboveLeaf111133320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113332) = true := by
  have h : ((childLL thetaAboveCell11113332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113332) h
theorem e24KC2ThetaAboveLeaf111133321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113332) = true := by
  have h : ((childLH thetaAboveCell11113332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113332) h
theorem e24KC2ThetaAboveLeaf111133322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113332) = true := by
  have h : ((childHL thetaAboveCell11113332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113332) h
theorem e24KC2ThetaAboveLeaf111133323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113332) = true := by
  have h : ((childHH thetaAboveCell11113332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113332) h
theorem e24KC2ThetaAboveLeaf111133330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113333) = true := by
  have h : ((childLL thetaAboveCell11113333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113333) h
theorem e24KC2ThetaAboveLeaf111133331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113333) = true := by
  have h : ((childLH thetaAboveCell11113333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113333) h
theorem e24KC2ThetaAboveLeaf111133332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113333) = true := by
  have h : ((childHL thetaAboveCell11113333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113333) h
theorem e24KC2ThetaAboveLeaf111133333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113333) = true := by
  have h : ((childHH thetaAboveCell11113333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113333) h
theorem e24KC2ThetaAboveLeaf1112000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1112))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1112))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1112))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1112))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1112))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1112))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1112))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1112))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf111202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1112)) = true := by
  have h : ((childHL (childLL thetaAboveCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1112)) h
theorem e24KC2ThetaAboveLeaf111203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1112)) = true := by
  have h : ((childHH (childLL thetaAboveCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1112)) h
theorem e24KC2ThetaAboveLeaf1112100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1112))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1112))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1112))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1112))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1112))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1112))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1112))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1112))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf111212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1112)) = true := by
  have h : ((childHL (childLH thetaAboveCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1112)) h
theorem e24KC2ThetaAboveLeaf111213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1112)) = true := by
  have h : ((childHH (childLH thetaAboveCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1112)) h
theorem e24KC2ThetaAboveLeaf11122 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1112) = true := by
  have h : ((childHL thetaAboveCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1112) h
theorem e24KC2ThetaAboveLeaf11123 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1112) = true := by
  have h : ((childHH thetaAboveCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1112) h
theorem e24KC2ThetaAboveLeaf1113000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1113))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1113))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1113))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1113))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1113))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1113))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1113))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1113))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf111302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1113)) = true := by
  have h : ((childHL (childLL thetaAboveCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1113)) h
theorem e24KC2ThetaAboveLeaf111303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1113)) = true := by
  have h : ((childHH (childLL thetaAboveCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1113)) h
theorem e24KC2ThetaAboveLeaf1113100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1113))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1113))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1113))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1113))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1113))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1113))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1113))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1113))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf111312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1113)) = true := by
  have h : ((childHL (childLH thetaAboveCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1113)) h
theorem e24KC2ThetaAboveLeaf111313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1113)) = true := by
  have h : ((childHH (childLH thetaAboveCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1113)) h
theorem e24KC2ThetaAboveLeaf11132 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1113) = true := by
  have h : ((childHL thetaAboveCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1113) h
theorem e24KC2ThetaAboveLeaf11133 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1113) = true := by
  have h : ((childHH thetaAboveCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1113) h
theorem e24KC2ThetaAboveLeaf1120 :
    adaptiveCoverCheck 15 thetaAboveCell1120 = true := by
  have h : (thetaAboveCell1120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1120 h
theorem e24KC2ThetaAboveLeaf1121 :
    adaptiveCoverCheck 15 thetaAboveCell1121 = true := by
  have h : (thetaAboveCell1121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1121 h
theorem e24KC2ThetaAboveLeaf1122 :
    adaptiveCoverCheck 15 thetaAboveCell1122 = true := by
  have h : (thetaAboveCell1122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1122 h
theorem e24KC2ThetaAboveLeaf1123 :
    adaptiveCoverCheck 15 thetaAboveCell1123 = true := by
  have h : (thetaAboveCell1123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1123 h
theorem e24KC2ThetaAboveLeaf1130 :
    adaptiveCoverCheck 15 thetaAboveCell1130 = true := by
  have h : (thetaAboveCell1130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1130 h
theorem e24KC2ThetaAboveLeaf1131 :
    adaptiveCoverCheck 15 thetaAboveCell1131 = true := by
  have h : (thetaAboveCell1131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1131 h
theorem e24KC2ThetaAboveLeaf1132 :
    adaptiveCoverCheck 15 thetaAboveCell1132 = true := by
  have h : (thetaAboveCell1132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1132 h
theorem e24KC2ThetaAboveLeaf1133 :
    adaptiveCoverCheck 15 thetaAboveCell1133 = true := by
  have h : (thetaAboveCell1133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1133 h
theorem e24KC2ThetaAboveLeaf120 :
    adaptiveCoverCheck 16 (childLL (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf121 :
    adaptiveCoverCheck 16 (childLH (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf122 :
    adaptiveCoverCheck 16 (childHL (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHL (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf123 :
    adaptiveCoverCheck 16 (childHH (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf130 :
    adaptiveCoverCheck 16 (childLL (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf131 :
    adaptiveCoverCheck 16 (childLH (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf132 :
    adaptiveCoverCheck 16 (childHL (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf133 :
    adaptiveCoverCheck 16 (childHH (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf200 :
    adaptiveCoverCheck 16 (childLL (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf201 :
    adaptiveCoverCheck 16 (childLH (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf202 :
    adaptiveCoverCheck 16 (childHL (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf203 :
    adaptiveCoverCheck 16 (childHH (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf210 :
    adaptiveCoverCheck 16 (childLL (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf211 :
    adaptiveCoverCheck 16 (childLH (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf212 :
    adaptiveCoverCheck 16 (childHL (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf213 :
    adaptiveCoverCheck 16 (childHH (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf220 :
    adaptiveCoverCheck 16 (childLL (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf221 :
    adaptiveCoverCheck 16 (childLH (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childHL e24ThetaAboveRoot))) h

theorem e24KC2ThetaAboveLeaf222 :
    adaptiveCoverCheck 16 (childHL (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHL (childHL e24ThetaAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childHL (childHL
    e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf223 :
    adaptiveCoverCheck 16 (childHH (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf230 :
    adaptiveCoverCheck 16 (childLL (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf231 :
    adaptiveCoverCheck 16 (childLH (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf232 :
    adaptiveCoverCheck 16 (childHL (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf233 :
    adaptiveCoverCheck 16 (childHH (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf300 :
    adaptiveCoverCheck 16 (childLL (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf301 :
    adaptiveCoverCheck 16 (childLH (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf302 :
    adaptiveCoverCheck 16 (childHL (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf303 :
    adaptiveCoverCheck 16 (childHH (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf310 :
    adaptiveCoverCheck 16 (childLL (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf311 :
    adaptiveCoverCheck 16 (childLH (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf312 :
    adaptiveCoverCheck 16 (childHL (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf313 :
    adaptiveCoverCheck 16 (childHH (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf320 :
    adaptiveCoverCheck 16 (childLL (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf321 :
    adaptiveCoverCheck 16 (childLH (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf322 :
    adaptiveCoverCheck 16 (childHL (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf323 :
    adaptiveCoverCheck 16 (childHH (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf330 :
    adaptiveCoverCheck 16 (childLL (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf331 :
    adaptiveCoverCheck 16 (childLH (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf332 :
    adaptiveCoverCheck 16 (childHL (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf333 :
    adaptiveCoverCheck 16 (childHH (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaBelowLeaf0000 :
    adaptiveCoverCheck 14 thetaBelowCell0000 = true := by
  have h : (thetaBelowCell0000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0000 h
theorem e24KC2ThetaBelowLeaf0001 :
    adaptiveCoverCheck 14 thetaBelowCell0001 = true := by
  have h : (thetaBelowCell0001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0001 h

theorem e24KC2ThetaBelowLeaf0002 :
    adaptiveCoverCheck 14 thetaBelowCell0002 = true := by
  have h : physicallyIrrelevant thetaBelowCell0002 = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 thetaBelowCell0002 h
theorem e24KC2ThetaBelowLeaf00030 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0003) = true := by
  have h : ((childLL thetaBelowCell0003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0003) h
theorem e24KC2ThetaBelowLeaf00031 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0003) = true := by
  have h : ((childLH thetaBelowCell0003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0003) h

theorem e24KC2ThetaBelowLeaf00032 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0003) = true := by
  have h : physicallyIrrelevant (childHL thetaBelowCell0003) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL thetaBelowCell0003) h
theorem e24KC2ThetaBelowLeaf00033 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0003) = true := by
  have h : ((childHH thetaBelowCell0003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0003) h
theorem e24KC2ThetaBelowLeaf00100 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0010) = true := by
  have h : ((childLL thetaBelowCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0010) h
theorem e24KC2ThetaBelowLeaf00101 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0010) = true := by
  have h : ((childLH thetaBelowCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0010) h
theorem e24KC2ThetaBelowLeaf00102 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0010) = true := by
  have h : ((childHL thetaBelowCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0010) h
theorem e24KC2ThetaBelowLeaf00103 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0010) = true := by
  have h : ((childHH thetaBelowCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0010) h
theorem e24KC2ThetaBelowLeaf00110 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0011) = true := by
  have h : ((childLL thetaBelowCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0011) h
theorem e24KC2ThetaBelowLeaf00111 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0011) = true := by
  have h : ((childLH thetaBelowCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0011) h
theorem e24KC2ThetaBelowLeaf00112 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0011) = true := by
  have h : ((childHL thetaBelowCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0011) h
theorem e24KC2ThetaBelowLeaf00113 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0011) = true := by
  have h : ((childHH thetaBelowCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0011) h
theorem e24KC2ThetaBelowLeaf00120 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0012) = true := by
  have h : ((childLL thetaBelowCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0012) h
theorem e24KC2ThetaBelowLeaf00121 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0012) = true := by
  have h : ((childLH thetaBelowCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0012) h
theorem e24KC2ThetaBelowLeaf00122 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0012) = true := by
  have h : ((childHL thetaBelowCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0012) h
theorem e24KC2ThetaBelowLeaf00123 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0012) = true := by
  have h : ((childHH thetaBelowCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0012) h
theorem e24KC2ThetaBelowLeaf00130 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0013) = true := by
  have h : ((childLL thetaBelowCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0013) h
theorem e24KC2ThetaBelowLeaf00131 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0013) = true := by
  have h : ((childLH thetaBelowCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0013) h
theorem e24KC2ThetaBelowLeaf00132 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0013) = true := by
  have h : ((childHL thetaBelowCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0013) h
theorem e24KC2ThetaBelowLeaf00133 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0013) = true := by
  have h : ((childHH thetaBelowCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0013) h

theorem e24KC2ThetaBelowLeaf002 :
    adaptiveCoverCheck 15 (childHL (childLL (childLL e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childLL e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childLL (childLL
    e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf0030 :
    adaptiveCoverCheck 14 thetaBelowCell0030 = true := by
  have h : (thetaBelowCell0030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0030 h
theorem e24KC2ThetaBelowLeaf0031 :
    adaptiveCoverCheck 14 thetaBelowCell0031 = true := by
  have h : (thetaBelowCell0031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0031 h

theorem e24KC2ThetaBelowLeaf0032 :
    adaptiveCoverCheck 14 thetaBelowCell0032 = true := by
  have h : physicallyIrrelevant thetaBelowCell0032 = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 thetaBelowCell0032 h
theorem e24KC2ThetaBelowLeaf0033 :
    adaptiveCoverCheck 14 thetaBelowCell0033 = true := by
  have h : (thetaBelowCell0033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0033 h
theorem e24KC2ThetaBelowLeaf01000 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0100) = true := by
  have h : ((childLL thetaBelowCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0100) h
theorem e24KC2ThetaBelowLeaf01001 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0100) = true := by
  have h : ((childLH thetaBelowCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0100) h
theorem e24KC2ThetaBelowLeaf01002 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0100) = true := by
  have h : ((childHL thetaBelowCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0100) h
theorem e24KC2ThetaBelowLeaf01003 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0100) = true := by
  have h : ((childHH thetaBelowCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0100) h
theorem e24KC2ThetaBelowLeaf01010 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0101) = true := by
  have h : ((childLL thetaBelowCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0101) h
theorem e24KC2ThetaBelowLeaf01011 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0101) = true := by
  have h : ((childLH thetaBelowCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0101) h
theorem e24KC2ThetaBelowLeaf01012 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0101) = true := by
  have h : ((childHL thetaBelowCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0101) h
theorem e24KC2ThetaBelowLeaf010130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell0101)) = true := by
  have h : ((childLL (childHH thetaBelowCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH thetaBelowCell0101)) h
theorem e24KC2ThetaBelowLeaf010131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell0101)) = true := by
  have h : ((childLH (childHH thetaBelowCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH thetaBelowCell0101)) h
theorem e24KC2ThetaBelowLeaf010132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell0101)) = true := by
  have h : ((childHL (childHH thetaBelowCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell0101)) h
theorem e24KC2ThetaBelowLeaf010133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell0101)) = true := by
  have h : ((childHH (childHH thetaBelowCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell0101)) h
theorem e24KC2ThetaBelowLeaf01020 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0102) = true := by
  have h : ((childLL thetaBelowCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0102) h
theorem e24KC2ThetaBelowLeaf01021 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0102) = true := by
  have h : ((childLH thetaBelowCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0102) h
theorem e24KC2ThetaBelowLeaf01022 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0102) = true := by
  have h : ((childHL thetaBelowCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0102) h
theorem e24KC2ThetaBelowLeaf01023 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0102) = true := by
  have h : ((childHH thetaBelowCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0102) h
theorem e24KC2ThetaBelowLeaf01030 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0103) = true := by
  have h : ((childLL thetaBelowCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0103) h
theorem e24KC2ThetaBelowLeaf01031 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0103) = true := by
  have h : ((childLH thetaBelowCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0103) h
theorem e24KC2ThetaBelowLeaf01032 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0103) = true := by
  have h : ((childHL thetaBelowCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0103) h
theorem e24KC2ThetaBelowLeaf01033 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0103) = true := by
  have h : ((childHH thetaBelowCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0103) h
theorem e24KC2ThetaBelowLeaf01100 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0110) = true := by
  have h : ((childLL thetaBelowCell0110)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0110) h
theorem e24KC2ThetaBelowLeaf011010 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell0110)) = true := by
  have h : ((childLL (childLH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011011 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell0110)) = true := by
  have h : ((childLH (childLH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell0110)) = true := by
  have h : ((childHL (childLH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell0110)) = true := by
  have h : ((childHH (childLH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell0110)) = true := by
  have h : ((childLL (childHL thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell0110)) = true := by
  have h : ((childLH (childHL thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell0110)) = true := by
  have h : ((childHL (childHL thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell0110)) = true := by
  have h : ((childHH (childHL thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell0110)) = true := by
  have h : ((childLL (childHH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell0110)) = true := by
  have h : ((childLH (childHH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell0110)) = true := by
  have h : ((childHL (childHH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell0110)) = true := by
  have h : ((childHH (childHH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell0111)) = true := by
  have h : ((childLL (childLL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell0111)) = true := by
  have h : ((childLH (childLL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell0111)) = true := by
  have h : ((childHL (childLL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell0111)) = true := by
  have h : ((childHH (childLL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell0111)) = true := by
  have h : ((childLL (childLH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell0111)) = true := by
  have h : ((childLH (childLH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell0111)) = true := by
  have h : ((childHL (childLH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell0111)) = true := by
  have h : ((childHH (childLH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell0111)) = true := by
  have h : ((childLL (childHL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell0111)) = true := by
  have h : ((childLH (childHL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell0111)) = true := by
  have h : ((childHL (childHL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell0111)) = true := by
  have h : ((childHH (childHL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell0111)) = true := by
  have h : ((childLL (childHH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell0111)) = true := by
  have h : ((childLH (childHH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell0111)) = true := by
  have h : ((childHL (childHH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell0111)) = true := by
  have h : ((childHH (childHH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf01120 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0112) = true := by
  have h : ((childLL thetaBelowCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0112) h
theorem e24KC2ThetaBelowLeaf01121 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0112) = true := by
  have h : ((childLH thetaBelowCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0112) h
theorem e24KC2ThetaBelowLeaf01122 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0112) = true := by
  have h : ((childHL thetaBelowCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0112) h
theorem e24KC2ThetaBelowLeaf01123 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0112) = true := by
  have h : ((childHH thetaBelowCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0112) h
theorem e24KC2ThetaBelowLeaf01130 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0113) = true := by
  have h : ((childLL thetaBelowCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0113) h
theorem e24KC2ThetaBelowLeaf01131 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0113) = true := by
  have h : ((childLH thetaBelowCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0113) h
theorem e24KC2ThetaBelowLeaf01132 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0113) = true := by
  have h : ((childHL thetaBelowCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0113) h
theorem e24KC2ThetaBelowLeaf01133 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0113) = true := by
  have h : ((childHH thetaBelowCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0113) h
theorem e24KC2ThetaBelowLeaf0120 :
    adaptiveCoverCheck 14 thetaBelowCell0120 = true := by
  have h : (thetaBelowCell0120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0120 h
theorem e24KC2ThetaBelowLeaf0121 :
    adaptiveCoverCheck 14 thetaBelowCell0121 = true := by
  have h : (thetaBelowCell0121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0121 h
theorem e24KC2ThetaBelowLeaf0122 :
    adaptiveCoverCheck 14 thetaBelowCell0122 = true := by
  have h : (thetaBelowCell0122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0122 h
theorem e24KC2ThetaBelowLeaf0123 :
    adaptiveCoverCheck 14 thetaBelowCell0123 = true := by
  have h : (thetaBelowCell0123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0123 h
theorem e24KC2ThetaBelowLeaf0130 :
    adaptiveCoverCheck 14 thetaBelowCell0130 = true := by
  have h : (thetaBelowCell0130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0130 h
theorem e24KC2ThetaBelowLeaf0131 :
    adaptiveCoverCheck 14 thetaBelowCell0131 = true := by
  have h : (thetaBelowCell0131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0131 h
theorem e24KC2ThetaBelowLeaf0132 :
    adaptiveCoverCheck 14 thetaBelowCell0132 = true := by
  have h : (thetaBelowCell0132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0132 h
theorem e24KC2ThetaBelowLeaf0133 :
    adaptiveCoverCheck 14 thetaBelowCell0133 = true := by
  have h : (thetaBelowCell0133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0133 h

theorem e24KC2ThetaBelowLeaf02 :
    adaptiveCoverCheck 16 (childHL (childLL e24ThetaBelowRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childLL e24ThetaBelowRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childLL e24ThetaBelowRoot)) h
theorem e24KC2ThetaBelowLeaf030 :
    adaptiveCoverCheck 15 (childLL (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHH (childLL e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf031 :
    adaptiveCoverCheck 15 (childLH (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childLL e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf032 :
    adaptiveCoverCheck 15 (childHL (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childLL e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childHH (childLL
    e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf033 :
    adaptiveCoverCheck 15 (childHH (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLL e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf100000 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1000)) = true := by
  have h : ((childLL (childLL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100001 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1000)) = true := by
  have h : ((childLH (childLL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100002 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1000)) = true := by
  have h : ((childHL (childLL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100003 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1000)) = true := by
  have h : ((childHH (childLL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100010 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1000)) = true := by
  have h : ((childLL (childLH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100011 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1000)) = true := by
  have h : ((childLH (childLH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1000)) = true := by
  have h : ((childHL (childLH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1000)) = true := by
  have h : ((childHH (childLH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1000)) = true := by
  have h : ((childLL (childHL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1000)) = true := by
  have h : ((childLH (childHL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1000)) = true := by
  have h : ((childHL (childHL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1000)) = true := by
  have h : ((childHH (childHL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1000)) = true := by
  have h : ((childLL (childHH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1000)) = true := by
  have h : ((childLH (childHH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1000)) = true := by
  have h : ((childHL (childHH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1000)) = true := by
  have h : ((childHH (childHH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1001)) = true := by
  have h : ((childLL (childLL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1001)) = true := by
  have h : ((childLH (childLL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1001)) = true := by
  have h : ((childHL (childLL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1001)) = true := by
  have h : ((childHH (childLL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1001)) = true := by
  have h : ((childLL (childLH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1001)) = true := by
  have h : ((childLH (childLH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1001)) = true := by
  have h : ((childHL (childLH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf1001130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1001))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1001))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1001))) = true := by
  have h : ((childHL (childHH (childLH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1001))) = true := by
  have h : ((childHH (childHH (childLH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf100120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1001)) = true := by
  have h : ((childLL (childHL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf1001210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1001))) = true := by
  have h : ((childLL (childLH (childHL thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1001))) = true := by
  have h : ((childLH (childLH (childHL thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1001))) = true := by
  have h : ((childHL (childLH (childHL thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1001))) = true := by
  have h : ((childHH (childLH (childHL thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf100122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1001)) = true := by
  have h : ((childHL (childHL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1001)) = true := by
  have h : ((childHH (childHL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf1001300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1001))) = true := by
  have h : ((childLL (childLL (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1001))) = true := by
  have h : ((childLH (childLL (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1001))) = true := by
  have h : ((childHL (childLL (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1001))) = true := by
  have h : ((childHH (childLL (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1001))) = true := by
  have h : ((childLL (childLH (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1001))) = true := by
  have h : ((childLH (childLH (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1001))) = true := by
  have h : ((childHL (childLH (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1001))) = true := by
  have h : ((childHH (childLH (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf100132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1001)) = true := by
  have h : ((childHL (childHH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1001)) = true := by
  have h : ((childHH (childHH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf10020 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1002) = true := by
  have h : ((childLL thetaBelowCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1002) h
theorem e24KC2ThetaBelowLeaf10021 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1002) = true := by
  have h : ((childLH thetaBelowCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell1002) h
theorem e24KC2ThetaBelowLeaf10022 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1002) = true := by
  have h : ((childHL thetaBelowCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1002) h
theorem e24KC2ThetaBelowLeaf10023 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1002) = true := by
  have h : ((childHH thetaBelowCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1002) h
theorem e24KC2ThetaBelowLeaf10030 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1003) = true := by
  have h : ((childLL thetaBelowCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1003) h
theorem e24KC2ThetaBelowLeaf100310 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1003)) = true := by
  have h : ((childLL (childLH thetaBelowCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1003)) h
theorem e24KC2ThetaBelowLeaf100311 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1003)) = true := by
  have h : ((childLH (childLH thetaBelowCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1003)) h
theorem e24KC2ThetaBelowLeaf100312 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1003)) = true := by
  have h : ((childHL (childLH thetaBelowCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1003)) h
theorem e24KC2ThetaBelowLeaf100313 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1003)) = true := by
  have h : ((childHH (childLH thetaBelowCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1003)) h
theorem e24KC2ThetaBelowLeaf10032 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1003) = true := by
  have h : ((childHL thetaBelowCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1003) h
theorem e24KC2ThetaBelowLeaf10033 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1003) = true := by
  have h : ((childHH thetaBelowCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1003) h
theorem e24KC2ThetaBelowLeaf101000 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1010)) = true := by
  have h : ((childLL (childLL thetaBelowCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1010)) h
theorem e24KC2ThetaBelowLeaf1010010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL thetaBelowCell1010))) = true := by
  have h : ((childLL (childLH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL thetaBelowCell1010))) = true := by
  have h : ((childLH (childLH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL thetaBelowCell1010))) = true := by
  have h : ((childHL (childLH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL thetaBelowCell1010))) = true := by
  have h : ((childHH (childLH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1010))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1010))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1010))) = true := by
  have h : ((childHL (childHL (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1010))) = true := by
  have h : ((childHH (childHL (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1010))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1010))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1010))) = true := by
  have h : ((childHL (childHH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1010))) = true := by
  have h : ((childHH (childHH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH thetaBelowCell1010))) = true := by
  have h : ((childLL (childLL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH thetaBelowCell1010))) = true := by
  have h : ((childLH (childLL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH thetaBelowCell1010))) = true := by
  have h : ((childHL (childLL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH thetaBelowCell1010))) = true := by
  have h : ((childHH (childLL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH thetaBelowCell1010))) = true := by
  have h : ((childLL (childLH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH thetaBelowCell1010))) = true := by
  have h : ((childLH (childLH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH thetaBelowCell1010))) = true := by
  have h : ((childHL (childLH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH thetaBelowCell1010))) = true := by
  have h : ((childHH (childLH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1010))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1010))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1010))) = true := by
  have h : ((childHL (childHL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1010))) = true := by
  have h : ((childHH (childHL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1010))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1010))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1010))) = true := by
  have h : ((childHL (childHH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1010))) = true := by
  have h : ((childHH (childHH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1010))) = true := by
  have h : ((childLL (childLL (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1010))) = true := by
  have h : ((childLH (childLL (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1010))) = true := by
  have h : ((childHL (childLL (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1010))) = true := by
  have h : ((childHH (childLL (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1010))) = true := by
  have h : ((childLL (childLH (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1010))) = true := by
  have h : ((childLH (childLH (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1010))) = true := by
  have h : ((childHL (childLH (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1010))) = true := by
  have h : ((childHH (childLH (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf101022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1010)) = true := by
  have h : ((childHL (childHL thetaBelowCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell1010)) h
theorem e24KC2ThetaBelowLeaf101023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1010)) = true := by
  have h : ((childHH (childHL thetaBelowCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell1010)) h
theorem e24KC2ThetaBelowLeaf1010300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1010))) = true := by
  have h : ((childLL (childLL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1010))) = true := by
  have h : ((childLH (childLL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1010))) = true := by
  have h : ((childHL (childLL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1010))) = true := by
  have h : ((childHH (childLL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1010))) = true := by
  have h : ((childLL (childLH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1010))) = true := by
  have h : ((childLH (childLH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1010))) = true := by
  have h : ((childHL (childLH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1010))) = true := by
  have h : ((childHH (childLH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1010))) = true := by
  have h : ((childLL (childHL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1010))) = true := by
  have h : ((childLH (childHL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1010))) = true := by
  have h : ((childHL (childHL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1010))) = true := by
  have h : ((childHH (childHL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1010))) = true := by
  have h : ((childLL (childHH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1010))) = true := by
  have h : ((childLH (childHH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1010))) = true := by
  have h : ((childHL (childHH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1010))) = true := by
  have h : ((childHH (childHH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1011000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL thetaBelowCell1011))) = true := by
  have h : ((childLL (childLL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL thetaBelowCell1011))) = true := by
  have h : ((childLH (childLL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL thetaBelowCell1011))) = true := by
  have h : ((childHL (childLL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL thetaBelowCell1011))) = true := by
  have h : ((childHH (childLL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf101101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1011)) = true := by
  have h : ((childLH (childLL thetaBelowCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1011)) h
theorem e24KC2ThetaBelowLeaf1011020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1011))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1011))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1011))) = true := by
  have h : ((childHL (childHL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1011))) = true := by
  have h : ((childHH (childHL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1011))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1011))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1011))) = true := by
  have h : ((childHL (childHH (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1011))) = true := by
  have h : ((childHH (childHH (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf101110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1011)) = true := by
  have h : ((childLL (childLH thetaBelowCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1011)) h
theorem e24KC2ThetaBelowLeaf101111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1011)) = true := by
  have h : ((childLH (childLH thetaBelowCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1011)) h
theorem e24KC2ThetaBelowLeaf1011120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1011))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1011))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1011))) = true := by
  have h : ((childHL (childHL (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1011))) = true := by
  have h : ((childHH (childHL (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1011))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1011))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1011))) = true := by
  have h : ((childHL (childHH (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1011))) = true := by
  have h : ((childHH (childHH (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1011))) = true := by
  have h : ((childLL (childLL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1011))) = true := by
  have h : ((childLH (childLL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1011))) = true := by
  have h : ((childHL (childLL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1011))) = true := by
  have h : ((childHH (childLL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1011))) = true := by
  have h : ((childLL (childLH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1011))) = true := by
  have h : ((childLH (childLH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1011))) = true := by
  have h : ((childHL (childLH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1011))) = true := by
  have h : ((childHH (childLH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1011))) = true := by
  have h : ((childLL (childHL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1011))) = true := by
  have h : ((childLH (childHL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL thetaBelowCell1011))) = true := by
  have h : ((childHL (childHL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL thetaBelowCell1011))) = true := by
  have h : ((childHH (childHL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1011))) = true := by
  have h : ((childLL (childHH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1011))) = true := by
  have h : ((childLH (childHH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL thetaBelowCell1011))) = true := by
  have h : ((childHL (childHH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL thetaBelowCell1011))) = true := by
  have h : ((childHH (childHH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1011))) = true := by
  have h : ((childLL (childLL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1011))) = true := by
  have h : ((childLH (childLL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1011))) = true := by
  have h : ((childHL (childLL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf10113030 :
    adaptiveCoverCheck 10 thetaBelowCell10113030 = true := by
  have h : (thetaBelowCell10113030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113030 h
theorem e24KC2ThetaBelowLeaf10113031 :
    adaptiveCoverCheck 10 thetaBelowCell10113031 = true := by
  have h : (thetaBelowCell10113031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113031 h
theorem e24KC2ThetaBelowLeaf10113032 :
    adaptiveCoverCheck 10 thetaBelowCell10113032 = true := by
  have h : (thetaBelowCell10113032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113032 h
theorem e24KC2ThetaBelowLeaf10113033 :
    adaptiveCoverCheck 10 thetaBelowCell10113033 = true := by
  have h : (thetaBelowCell10113033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113033 h
theorem e24KC2ThetaBelowLeaf1011310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1011))) = true := by
  have h : ((childLL (childLH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf10113110 :
    adaptiveCoverCheck 10 thetaBelowCell10113110 = true := by
  have h : (thetaBelowCell10113110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113110 h
theorem e24KC2ThetaBelowLeaf10113111 :
    adaptiveCoverCheck 10 thetaBelowCell10113111 = true := by
  have h : (thetaBelowCell10113111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113111 h
theorem e24KC2ThetaBelowLeaf10113112 :
    adaptiveCoverCheck 10 thetaBelowCell10113112 = true := by
  have h : (thetaBelowCell10113112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113112 h
theorem e24KC2ThetaBelowLeaf10113113 :
    adaptiveCoverCheck 10 thetaBelowCell10113113 = true := by
  have h : (thetaBelowCell10113113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113113 h
theorem e24KC2ThetaBelowLeaf10113120 :
    adaptiveCoverCheck 10 thetaBelowCell10113120 = true := by
  have h : (thetaBelowCell10113120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113120 h
theorem e24KC2ThetaBelowLeaf10113121 :
    adaptiveCoverCheck 10 thetaBelowCell10113121 = true := by
  have h : (thetaBelowCell10113121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113121 h
theorem e24KC2ThetaBelowLeaf10113122 :
    adaptiveCoverCheck 10 thetaBelowCell10113122 = true := by
  have h : (thetaBelowCell10113122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113122 h
theorem e24KC2ThetaBelowLeaf10113123 :
    adaptiveCoverCheck 10 thetaBelowCell10113123 = true := by
  have h : (thetaBelowCell10113123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113123 h
theorem e24KC2ThetaBelowLeaf10113130 :
    adaptiveCoverCheck 10 thetaBelowCell10113130 = true := by
  have h : (thetaBelowCell10113130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113130 h
theorem e24KC2ThetaBelowLeaf10113131 :
    adaptiveCoverCheck 10 thetaBelowCell10113131 = true := by
  have h : (thetaBelowCell10113131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113131 h
theorem e24KC2ThetaBelowLeaf10113132 :
    adaptiveCoverCheck 10 thetaBelowCell10113132 = true := by
  have h : (thetaBelowCell10113132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113132 h
theorem e24KC2ThetaBelowLeaf10113133 :
    adaptiveCoverCheck 10 thetaBelowCell10113133 = true := by
  have h : (thetaBelowCell10113133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113133 h
theorem e24KC2ThetaBelowLeaf1011320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1011))) = true := by
  have h : ((childLL (childHL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1011))) = true := by
  have h : ((childLH (childHL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1011))) = true := by
  have h : ((childHL (childHL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1011))) = true := by
  have h : ((childHH (childHL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1011))) = true := by
  have h : ((childLL (childHH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1011))) = true := by
  have h : ((childLH (childHH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1011))) = true := by
  have h : ((childHL (childHH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1011))) = true := by
  have h : ((childHH (childHH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf101200 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1012)) = true := by
  have h : ((childLL (childLL thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101201 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1012)) = true := by
  have h : ((childLH (childLL thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101202 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1012)) = true := by
  have h : ((childHL (childLL thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101203 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1012)) = true := by
  have h : ((childHH (childLL thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101210 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1012)) = true := by
  have h : ((childLL (childLH thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101211 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1012)) = true := by
  have h : ((childLH (childLH thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101212 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1012)) = true := by
  have h : ((childHL (childLH thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101213 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1012)) = true := by
  have h : ((childHH (childLH thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf10122 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1012) = true := by
  have h : ((childHL thetaBelowCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1012) h
theorem e24KC2ThetaBelowLeaf10123 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1012) = true := by
  have h : ((childHH thetaBelowCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1012) h
theorem e24KC2ThetaBelowLeaf101300 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1013)) = true := by
  have h : ((childLL (childLL thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101301 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1013)) = true := by
  have h : ((childLH (childLL thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101302 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1013)) = true := by
  have h : ((childHL (childLL thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101303 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1013)) = true := by
  have h : ((childHH (childLL thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101310 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1013)) = true := by
  have h : ((childLL (childLH thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101311 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1013)) = true := by
  have h : ((childLH (childLH thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101312 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1013)) = true := by
  have h : ((childHL (childLH thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101313 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1013)) = true := by
  have h : ((childHH (childLH thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf10132 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1013) = true := by
  have h : ((childHL thetaBelowCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1013) h
theorem e24KC2ThetaBelowLeaf10133 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1013) = true := by
  have h : ((childHH thetaBelowCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1013) h
theorem e24KC2ThetaBelowLeaf1020 :
    adaptiveCoverCheck 14 thetaBelowCell1020 = true := by
  have h : (thetaBelowCell1020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1020 h
theorem e24KC2ThetaBelowLeaf1021 :
    adaptiveCoverCheck 14 thetaBelowCell1021 = true := by
  have h : (thetaBelowCell1021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1021 h
theorem e24KC2ThetaBelowLeaf1022 :
    adaptiveCoverCheck 14 thetaBelowCell1022 = true := by
  have h : (thetaBelowCell1022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1022 h

end PartE
end GerverSofa

end

end

end
