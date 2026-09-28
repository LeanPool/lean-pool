/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT153600006`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells502d119e99

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0012 : AngleCell :=
  childHL (childLH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0013 : AngleCell :=
  childHH (childLH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0020 : AngleCell :=
  childLL (childHL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0021 : AngleCell :=
  childLH (childHL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0022 : AngleCell :=
  childHL (childHL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0023 : AngleCell :=
  childHH (childHL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0030 : AngleCell :=
  childLL (childHH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0031 : AngleCell :=
  childLH (childHH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0032 : AngleCell :=
  childHL (childHH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0033 : AngleCell :=
  childHH (childHH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `00112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0011)))
/-- Subcell `00113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0011)))
/-- Subcell `00113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0011)))
/-- Subcell `00113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0011)))
/-- Subcell `00113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0011)))
/-- Subcell `00113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0011)))
/-- Subcell `00113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0011)))
/-- Subcell `00113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0011)))
/-- Subcell `00113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0011)))
/-- Subcell `00113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0011)))
/-- Subcell `00113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0011)))
/-- Subcell `00113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0011)))
/-- Subcell `00113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0011)))
/-- Subcell `00113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0011)))
/-- Subcell `00113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0011)))
/-- Subcell `00113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0011)))
/-- Subcell `00113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0011)))
/-- Subcell `00113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0011)))
/-- Subcell `00113333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0011)))
/-- Subcell `01002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0100)))
/-- Subcell `01002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0100)))
/-- Subcell `01002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0100)))
/-- Subcell `01002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0100)))
/-- Subcell `01002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0100)))
/-- Subcell `01002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0100)))
/-- Subcell `01002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0100)))
/-- Subcell `01002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0100)))
/-- Subcell `01002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0100)))
/-- Subcell `01002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0100)))
/-- Subcell `01002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0100)))
/-- Subcell `01002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0100)))
/-- Subcell `01002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0100)))
/-- Subcell `01002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0100)))
/-- Subcell `01002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0100)))
/-- Subcell `01002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0100)))
/-- Subcell `01002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0100)))
/-- Subcell `01002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01002333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0100)))
/-- Subcell `01003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0100)))
/-- Subcell `01003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0100)))
/-- Subcell `01003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0100)))
/-- Subcell `01003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0100)))
/-- Subcell `01003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0100)))
/-- Subcell `01003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0100)))
/-- Subcell `01003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0100)))
/-- Subcell `01003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0100)))
/-- Subcell `01003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0100)))
/-- Subcell `01003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0100)))
/-- Subcell `01003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0100)))
/-- Subcell `01003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0100)))
/-- Subcell `01003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0100)))
/-- Subcell `01003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0100)))
/-- Subcell `01003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0100)))
/-- Subcell `01003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0100)))
/-- Subcell `01003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0100)))
/-- Subcell `01003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0100)))
/-- Subcell `01003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0100)))

end CertificateCells502d119e99

open CertificateCells502d119e99
theorem e24KC2ThetaAboveLeaf001123133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00112313) = true := by
  have h : ((childHH thetaAboveCell00112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00112313) h
theorem e24KC2ThetaAboveLeaf00112320 :
    adaptiveCoverCheck 11 thetaAboveCell00112320 = true := by
  have h : (thetaAboveCell00112320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112320 h
theorem e24KC2ThetaAboveLeaf00112321 :
    adaptiveCoverCheck 11 thetaAboveCell00112321 = true := by
  have h : (thetaAboveCell00112321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112321 h
theorem e24KC2ThetaAboveLeaf00112322 :
    adaptiveCoverCheck 11 thetaAboveCell00112322 = true := by
  have h : (thetaAboveCell00112322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112322 h
theorem e24KC2ThetaAboveLeaf00112323 :
    adaptiveCoverCheck 11 thetaAboveCell00112323 = true := by
  have h : (thetaAboveCell00112323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112323 h
theorem e24KC2ThetaAboveLeaf00112330 :
    adaptiveCoverCheck 11 thetaAboveCell00112330 = true := by
  have h : (thetaAboveCell00112330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112330 h
theorem e24KC2ThetaAboveLeaf00112331 :
    adaptiveCoverCheck 11 thetaAboveCell00112331 = true := by
  have h : (thetaAboveCell00112331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112331 h
theorem e24KC2ThetaAboveLeaf00112332 :
    adaptiveCoverCheck 11 thetaAboveCell00112332 = true := by
  have h : (thetaAboveCell00112332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112332 h
theorem e24KC2ThetaAboveLeaf00112333 :
    adaptiveCoverCheck 11 thetaAboveCell00112333 = true := by
  have h : (thetaAboveCell00112333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112333 h
theorem e24KC2ThetaAboveLeaf0011300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0011))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0011))) h
theorem e24KC2ThetaAboveLeaf0011301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0011))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0011))) h
theorem e24KC2ThetaAboveLeaf00113020 :
    adaptiveCoverCheck 11 thetaAboveCell00113020 = true := by
  have h : (thetaAboveCell00113020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113020 h
theorem e24KC2ThetaAboveLeaf00113021 :
    adaptiveCoverCheck 11 thetaAboveCell00113021 = true := by
  have h : (thetaAboveCell00113021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113021 h
theorem e24KC2ThetaAboveLeaf00113022 :
    adaptiveCoverCheck 11 thetaAboveCell00113022 = true := by
  have h : (thetaAboveCell00113022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113022 h
theorem e24KC2ThetaAboveLeaf00113023 :
    adaptiveCoverCheck 11 thetaAboveCell00113023 = true := by
  have h : (thetaAboveCell00113023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113023 h
theorem e24KC2ThetaAboveLeaf00113030 :
    adaptiveCoverCheck 11 thetaAboveCell00113030 = true := by
  have h : (thetaAboveCell00113030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113030 h
theorem e24KC2ThetaAboveLeaf00113031 :
    adaptiveCoverCheck 11 thetaAboveCell00113031 = true := by
  have h : (thetaAboveCell00113031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113031 h
theorem e24KC2ThetaAboveLeaf00113032 :
    adaptiveCoverCheck 11 thetaAboveCell00113032 = true := by
  have h : (thetaAboveCell00113032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113032 h
theorem e24KC2ThetaAboveLeaf00113033 :
    adaptiveCoverCheck 11 thetaAboveCell00113033 = true := by
  have h : (thetaAboveCell00113033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113033 h
theorem e24KC2ThetaAboveLeaf0011310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0011))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0011))) h
theorem e24KC2ThetaAboveLeaf0011311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0011))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0011))) h
theorem e24KC2ThetaAboveLeaf00113120 :
    adaptiveCoverCheck 11 thetaAboveCell00113120 = true := by
  have h : (thetaAboveCell00113120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113120 h
theorem e24KC2ThetaAboveLeaf00113121 :
    adaptiveCoverCheck 11 thetaAboveCell00113121 = true := by
  have h : (thetaAboveCell00113121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113121 h
theorem e24KC2ThetaAboveLeaf00113122 :
    adaptiveCoverCheck 11 thetaAboveCell00113122 = true := by
  have h : (thetaAboveCell00113122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113122 h
theorem e24KC2ThetaAboveLeaf00113123 :
    adaptiveCoverCheck 11 thetaAboveCell00113123 = true := by
  have h : (thetaAboveCell00113123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113123 h
theorem e24KC2ThetaAboveLeaf00113130 :
    adaptiveCoverCheck 11 thetaAboveCell00113130 = true := by
  have h : (thetaAboveCell00113130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113130 h
theorem e24KC2ThetaAboveLeaf00113131 :
    adaptiveCoverCheck 11 thetaAboveCell00113131 = true := by
  have h : (thetaAboveCell00113131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113131 h
theorem e24KC2ThetaAboveLeaf00113132 :
    adaptiveCoverCheck 11 thetaAboveCell00113132 = true := by
  have h : (thetaAboveCell00113132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113132 h
theorem e24KC2ThetaAboveLeaf00113133 :
    adaptiveCoverCheck 11 thetaAboveCell00113133 = true := by
  have h : (thetaAboveCell00113133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113133 h
theorem e24KC2ThetaAboveLeaf001132000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00113200) = true := by
  have h : ((childLL thetaAboveCell00113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00113200) h
theorem e24KC2ThetaAboveLeaf001132001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00113200) = true := by
  have h : ((childLH thetaAboveCell00113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00113200) h
theorem e24KC2ThetaAboveLeaf0011320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00113200)) = true := by
  have h : ((childLL (childHL thetaAboveCell00113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell00113200)) h
theorem e24KC2ThetaAboveLeaf0011320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00113200)) = true := by
  have h : ((childLH (childHL thetaAboveCell00113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00113200)) h
theorem e24KC2ThetaAboveLeaf0011320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00113200)) = true := by
  have h : ((childLL (childHH thetaAboveCell00113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00113200)) h
theorem e24KC2ThetaAboveLeaf0011320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00113200)) = true := by
  have h : ((childLH (childHH thetaAboveCell00113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00113200)) h
theorem e24KC2ThetaAboveLeaf001132010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00113201) = true := by
  have h : ((childLL thetaAboveCell00113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00113201) h
theorem e24KC2ThetaAboveLeaf001132011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00113201) = true := by
  have h : ((childLH thetaAboveCell00113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00113201) h
theorem e24KC2ThetaAboveLeaf0011320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00113201)) = true := by
  have h : ((childLL (childHL thetaAboveCell00113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell00113201)) h
theorem e24KC2ThetaAboveLeaf0011320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00113201)) = true := by
  have h : ((childLH (childHL thetaAboveCell00113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00113201)) h
theorem e24KC2ThetaAboveLeaf0011320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00113201)) = true := by
  have h : ((childLL (childHH thetaAboveCell00113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00113201)) h
theorem e24KC2ThetaAboveLeaf0011320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00113201)) = true := by
  have h : ((childLH (childHH thetaAboveCell00113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00113201)) h
theorem e24KC2ThetaAboveLeaf0011320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00113202)) = true := by
  have h : ((childHL (childLL thetaAboveCell00113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00113202)) h
theorem e24KC2ThetaAboveLeaf0011320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00113202)) = true := by
  have h : ((childHH (childLL thetaAboveCell00113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00113202)) h
theorem e24KC2ThetaAboveLeaf0011320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00113202)) = true := by
  have h : ((childHL (childLH thetaAboveCell00113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00113202)) h
theorem e24KC2ThetaAboveLeaf0011320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00113202)) = true := by
  have h : ((childHH (childLH thetaAboveCell00113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00113202)) h
theorem e24KC2ThetaAboveLeaf001132022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00113202) = true := by
  have h : ((childHL thetaAboveCell00113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00113202) h
theorem e24KC2ThetaAboveLeaf001132023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00113202) = true := by
  have h : ((childHH thetaAboveCell00113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00113202) h
theorem e24KC2ThetaAboveLeaf0011320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00113203)) = true := by
  have h : ((childHL (childLL thetaAboveCell00113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00113203)) h
theorem e24KC2ThetaAboveLeaf0011320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00113203)) = true := by
  have h : ((childHH (childLL thetaAboveCell00113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00113203)) h
theorem e24KC2ThetaAboveLeaf0011320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00113203)) = true := by
  have h : ((childHL (childLH thetaAboveCell00113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00113203)) h
theorem e24KC2ThetaAboveLeaf0011320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00113203)) = true := by
  have h : ((childHH (childLH thetaAboveCell00113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00113203)) h
theorem e24KC2ThetaAboveLeaf001132032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00113203) = true := by
  have h : ((childHL thetaAboveCell00113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00113203) h
theorem e24KC2ThetaAboveLeaf001132033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00113203) = true := by
  have h : ((childHH thetaAboveCell00113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00113203) h
theorem e24KC2ThetaAboveLeaf001132100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00113210) = true := by
  have h : ((childLL thetaAboveCell00113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00113210) h
theorem e24KC2ThetaAboveLeaf001132101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00113210) = true := by
  have h : ((childLH thetaAboveCell00113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00113210) h
theorem e24KC2ThetaAboveLeaf0011321020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00113210)) = true := by
  have h : ((childLL (childHL thetaAboveCell00113210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell00113210)) h
theorem e24KC2ThetaAboveLeaf0011321021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00113210)) = true := by
  have h : ((childLH (childHL thetaAboveCell00113210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00113210)) h
theorem e24KC2ThetaAboveLeaf0011321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00113210)) = true := by
  have h : ((childLL (childHH thetaAboveCell00113210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00113210)) h
theorem e24KC2ThetaAboveLeaf0011321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00113210)) = true := by
  have h : ((childLH (childHH thetaAboveCell00113210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00113210)) h
theorem e24KC2ThetaAboveLeaf001132110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00113211) = true := by
  have h : ((childLL thetaAboveCell00113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00113211) h
theorem e24KC2ThetaAboveLeaf001132111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00113211) = true := by
  have h : ((childLH thetaAboveCell00113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00113211) h
theorem e24KC2ThetaAboveLeaf0011321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00113211)) = true := by
  have h : ((childLL (childHL thetaAboveCell00113211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell00113211)) h
theorem e24KC2ThetaAboveLeaf0011321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00113211)) = true := by
  have h : ((childLH (childHL thetaAboveCell00113211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00113211)) h
theorem e24KC2ThetaAboveLeaf0011321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00113211)) = true := by
  have h : ((childLL (childHH thetaAboveCell00113211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00113211)) h
theorem e24KC2ThetaAboveLeaf0011321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00113211)) = true := by
  have h : ((childLH (childHH thetaAboveCell00113211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00113211)) h
theorem e24KC2ThetaAboveLeaf0011321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00113212)) = true := by
  have h : ((childHL (childLL thetaAboveCell00113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00113212)) h
theorem e24KC2ThetaAboveLeaf0011321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00113212)) = true := by
  have h : ((childHH (childLL thetaAboveCell00113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00113212)) h
theorem e24KC2ThetaAboveLeaf0011321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00113212)) = true := by
  have h : ((childHL (childLH thetaAboveCell00113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00113212)) h
theorem e24KC2ThetaAboveLeaf0011321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00113212)) = true := by
  have h : ((childHH (childLH thetaAboveCell00113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00113212)) h
theorem e24KC2ThetaAboveLeaf001132122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00113212) = true := by
  have h : ((childHL thetaAboveCell00113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00113212) h
theorem e24KC2ThetaAboveLeaf001132123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00113212) = true := by
  have h : ((childHH thetaAboveCell00113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00113212) h
theorem e24KC2ThetaAboveLeaf0011321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00113213)) = true := by
  have h : ((childHL (childLL thetaAboveCell00113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00113213)) h
theorem e24KC2ThetaAboveLeaf0011321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00113213)) = true := by
  have h : ((childHH (childLL thetaAboveCell00113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00113213)) h
theorem e24KC2ThetaAboveLeaf0011321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00113213)) = true := by
  have h : ((childHL (childLH thetaAboveCell00113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00113213)) h
theorem e24KC2ThetaAboveLeaf0011321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00113213)) = true := by
  have h : ((childHH (childLH thetaAboveCell00113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00113213)) h
theorem e24KC2ThetaAboveLeaf001132132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00113213) = true := by
  have h : ((childHL thetaAboveCell00113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00113213) h
theorem e24KC2ThetaAboveLeaf001132133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00113213) = true := by
  have h : ((childHH thetaAboveCell00113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00113213) h
theorem e24KC2ThetaAboveLeaf00113220 :
    adaptiveCoverCheck 11 thetaAboveCell00113220 = true := by
  have h : (thetaAboveCell00113220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113220 h
theorem e24KC2ThetaAboveLeaf00113221 :
    adaptiveCoverCheck 11 thetaAboveCell00113221 = true := by
  have h : (thetaAboveCell00113221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113221 h
theorem e24KC2ThetaAboveLeaf00113222 :
    adaptiveCoverCheck 11 thetaAboveCell00113222 = true := by
  have h : (thetaAboveCell00113222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113222 h
theorem e24KC2ThetaAboveLeaf00113223 :
    adaptiveCoverCheck 11 thetaAboveCell00113223 = true := by
  have h : (thetaAboveCell00113223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113223 h
theorem e24KC2ThetaAboveLeaf00113230 :
    adaptiveCoverCheck 11 thetaAboveCell00113230 = true := by
  have h : (thetaAboveCell00113230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113230 h
theorem e24KC2ThetaAboveLeaf00113231 :
    adaptiveCoverCheck 11 thetaAboveCell00113231 = true := by
  have h : (thetaAboveCell00113231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113231 h
theorem e24KC2ThetaAboveLeaf00113232 :
    adaptiveCoverCheck 11 thetaAboveCell00113232 = true := by
  have h : (thetaAboveCell00113232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113232 h
theorem e24KC2ThetaAboveLeaf00113233 :
    adaptiveCoverCheck 11 thetaAboveCell00113233 = true := by
  have h : (thetaAboveCell00113233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113233 h
theorem e24KC2ThetaAboveLeaf001133000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00113300) = true := by
  have h : ((childLL thetaAboveCell00113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00113300) h
theorem e24KC2ThetaAboveLeaf001133001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00113300) = true := by
  have h : ((childLH thetaAboveCell00113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00113300) h
theorem e24KC2ThetaAboveLeaf0011330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00113300)) = true := by
  have h : ((childLL (childHL thetaAboveCell00113300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell00113300)) h
theorem e24KC2ThetaAboveLeaf0011330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00113300)) = true := by
  have h : ((childLH (childHL thetaAboveCell00113300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00113300)) h
theorem e24KC2ThetaAboveLeaf0011330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00113300)) = true := by
  have h : ((childLL (childHH thetaAboveCell00113300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00113300)) h
theorem e24KC2ThetaAboveLeaf0011330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00113300)) = true := by
  have h : ((childLH (childHH thetaAboveCell00113300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00113300)) h
theorem e24KC2ThetaAboveLeaf001133010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00113301) = true := by
  have h : ((childLL thetaAboveCell00113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00113301) h
theorem e24KC2ThetaAboveLeaf001133011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00113301) = true := by
  have h : ((childLH thetaAboveCell00113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00113301) h
theorem e24KC2ThetaAboveLeaf0011330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00113301)) = true := by
  have h : ((childLL (childHL thetaAboveCell00113301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell00113301)) h
theorem e24KC2ThetaAboveLeaf0011330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00113301)) = true := by
  have h : ((childLH (childHL thetaAboveCell00113301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00113301)) h
theorem e24KC2ThetaAboveLeaf0011330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00113301)) = true := by
  have h : ((childLL (childHH thetaAboveCell00113301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00113301)) h
theorem e24KC2ThetaAboveLeaf0011330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00113301)) = true := by
  have h : ((childLH (childHH thetaAboveCell00113301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00113301)) h
theorem e24KC2ThetaAboveLeaf0011330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00113302)) = true := by
  have h : ((childHL (childLL thetaAboveCell00113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00113302)) h
theorem e24KC2ThetaAboveLeaf0011330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00113302)) = true := by
  have h : ((childHH (childLL thetaAboveCell00113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00113302)) h
theorem e24KC2ThetaAboveLeaf0011330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00113302)) = true := by
  have h : ((childHL (childLH thetaAboveCell00113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00113302)) h
theorem e24KC2ThetaAboveLeaf0011330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00113302)) = true := by
  have h : ((childHH (childLH thetaAboveCell00113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00113302)) h
theorem e24KC2ThetaAboveLeaf001133022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00113302) = true := by
  have h : ((childHL thetaAboveCell00113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00113302) h
theorem e24KC2ThetaAboveLeaf001133023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00113302) = true := by
  have h : ((childHH thetaAboveCell00113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00113302) h
theorem e24KC2ThetaAboveLeaf0011330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00113303)) = true := by
  have h : ((childHL (childLL thetaAboveCell00113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00113303)) h
theorem e24KC2ThetaAboveLeaf0011330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00113303)) = true := by
  have h : ((childHH (childLL thetaAboveCell00113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00113303)) h
theorem e24KC2ThetaAboveLeaf0011330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00113303)) = true := by
  have h : ((childHL (childLH thetaAboveCell00113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00113303)) h
theorem e24KC2ThetaAboveLeaf0011330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00113303)) = true := by
  have h : ((childHH (childLH thetaAboveCell00113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00113303)) h
theorem e24KC2ThetaAboveLeaf001133032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00113303) = true := by
  have h : ((childHL thetaAboveCell00113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00113303) h
theorem e24KC2ThetaAboveLeaf001133033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00113303) = true := by
  have h : ((childHH thetaAboveCell00113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00113303) h
theorem e24KC2ThetaAboveLeaf001133100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00113310) = true := by
  have h : ((childLL thetaAboveCell00113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00113310) h
theorem e24KC2ThetaAboveLeaf001133101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00113310) = true := by
  have h : ((childLH thetaAboveCell00113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00113310) h
theorem e24KC2ThetaAboveLeaf0011331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00113310)) = true := by
  have h : ((childLL (childHL thetaAboveCell00113310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell00113310)) h
theorem e24KC2ThetaAboveLeaf0011331021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00113310)) = true := by
  have h : ((childLH (childHL thetaAboveCell00113310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00113310)) h
theorem e24KC2ThetaAboveLeaf0011331030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00113310)) = true := by
  have h : ((childLL (childHH thetaAboveCell00113310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00113310)) h
theorem e24KC2ThetaAboveLeaf0011331031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00113310)) = true := by
  have h : ((childLH (childHH thetaAboveCell00113310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00113310)) h
theorem e24KC2ThetaAboveLeaf001133110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00113311) = true := by
  have h : ((childLL thetaAboveCell00113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00113311) h
theorem e24KC2ThetaAboveLeaf001133111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00113311) = true := by
  have h : ((childLH thetaAboveCell00113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00113311) h
theorem e24KC2ThetaAboveLeaf0011331120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00113311)) = true := by
  have h : ((childLL (childHL thetaAboveCell00113311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell00113311)) h
theorem e24KC2ThetaAboveLeaf0011331121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00113311)) = true := by
  have h : ((childLH (childHL thetaAboveCell00113311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00113311)) h
theorem e24KC2ThetaAboveLeaf0011331130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00113311)) = true := by
  have h : ((childLL (childHH thetaAboveCell00113311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00113311)) h
theorem e24KC2ThetaAboveLeaf0011331131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00113311)) = true := by
  have h : ((childLH (childHH thetaAboveCell00113311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00113311)) h
theorem e24KC2ThetaAboveLeaf0011331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00113312)) = true := by
  have h : ((childHL (childLL thetaAboveCell00113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00113312)) h
theorem e24KC2ThetaAboveLeaf0011331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00113312)) = true := by
  have h : ((childHH (childLL thetaAboveCell00113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00113312)) h
theorem e24KC2ThetaAboveLeaf0011331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00113312)) = true := by
  have h : ((childHL (childLH thetaAboveCell00113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00113312)) h
theorem e24KC2ThetaAboveLeaf0011331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00113312)) = true := by
  have h : ((childHH (childLH thetaAboveCell00113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00113312)) h
theorem e24KC2ThetaAboveLeaf001133122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00113312) = true := by
  have h : ((childHL thetaAboveCell00113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00113312) h
theorem e24KC2ThetaAboveLeaf001133123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00113312) = true := by
  have h : ((childHH thetaAboveCell00113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00113312) h
theorem e24KC2ThetaAboveLeaf0011331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00113313)) = true := by
  have h : ((childHL (childLL thetaAboveCell00113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00113313)) h
theorem e24KC2ThetaAboveLeaf0011331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00113313)) = true := by
  have h : ((childHH (childLL thetaAboveCell00113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00113313)) h
theorem e24KC2ThetaAboveLeaf0011331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00113313)) = true := by
  have h : ((childHL (childLH thetaAboveCell00113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00113313)) h
theorem e24KC2ThetaAboveLeaf0011331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00113313)) = true := by
  have h : ((childHH (childLH thetaAboveCell00113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00113313)) h
theorem e24KC2ThetaAboveLeaf001133132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00113313) = true := by
  have h : ((childHL thetaAboveCell00113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00113313) h
theorem e24KC2ThetaAboveLeaf001133133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00113313) = true := by
  have h : ((childHH thetaAboveCell00113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00113313) h
theorem e24KC2ThetaAboveLeaf00113320 :
    adaptiveCoverCheck 11 thetaAboveCell00113320 = true := by
  have h : (thetaAboveCell00113320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113320 h
theorem e24KC2ThetaAboveLeaf00113321 :
    adaptiveCoverCheck 11 thetaAboveCell00113321 = true := by
  have h : (thetaAboveCell00113321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113321 h
theorem e24KC2ThetaAboveLeaf00113322 :
    adaptiveCoverCheck 11 thetaAboveCell00113322 = true := by
  have h : (thetaAboveCell00113322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113322 h
theorem e24KC2ThetaAboveLeaf00113323 :
    adaptiveCoverCheck 11 thetaAboveCell00113323 = true := by
  have h : (thetaAboveCell00113323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113323 h
theorem e24KC2ThetaAboveLeaf00113330 :
    adaptiveCoverCheck 11 thetaAboveCell00113330 = true := by
  have h : (thetaAboveCell00113330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113330 h
theorem e24KC2ThetaAboveLeaf00113331 :
    adaptiveCoverCheck 11 thetaAboveCell00113331 = true := by
  have h : (thetaAboveCell00113331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113331 h
theorem e24KC2ThetaAboveLeaf00113332 :
    adaptiveCoverCheck 11 thetaAboveCell00113332 = true := by
  have h : (thetaAboveCell00113332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113332 h
theorem e24KC2ThetaAboveLeaf00113333 :
    adaptiveCoverCheck 11 thetaAboveCell00113333 = true := by
  have h : (thetaAboveCell00113333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00113333 h
theorem e24KC2ThetaAboveLeaf0012000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0012))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0012))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0012))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0012))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0012))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0012))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0012))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0012))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf001202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0012)) = true := by
  have h : ((childHL (childLL thetaAboveCell0012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0012)) h
theorem e24KC2ThetaAboveLeaf001203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0012)) = true := by
  have h : ((childHH (childLL thetaAboveCell0012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0012)) h
theorem e24KC2ThetaAboveLeaf0012100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0012))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0012))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0012))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0012))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0012))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0012))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0012))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf0012113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0012))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0012))) h
theorem e24KC2ThetaAboveLeaf001212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0012)) = true := by
  have h : ((childHL (childLH thetaAboveCell0012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0012)) h
theorem e24KC2ThetaAboveLeaf001213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0012)) = true := by
  have h : ((childHH (childLH thetaAboveCell0012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0012)) h
theorem e24KC2ThetaAboveLeaf00122 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0012) = true := by
  have h : ((childHL thetaAboveCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0012) h
theorem e24KC2ThetaAboveLeaf00123 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0012) = true := by
  have h : ((childHH thetaAboveCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0012) h
theorem e24KC2ThetaAboveLeaf0013000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0013))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0013))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0013))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0013))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0013))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0013))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0013))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0013))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf001302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0013)) = true := by
  have h : ((childHL (childLL thetaAboveCell0013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0013)) h
theorem e24KC2ThetaAboveLeaf001303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0013)) = true := by
  have h : ((childHH (childLL thetaAboveCell0013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0013)) h
theorem e24KC2ThetaAboveLeaf0013100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0013))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0013))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0013))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0013))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0013))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0013))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0013))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf0013113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0013))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0013))) h
theorem e24KC2ThetaAboveLeaf001312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0013)) = true := by
  have h : ((childHL (childLH thetaAboveCell0013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0013)) h
theorem e24KC2ThetaAboveLeaf001313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0013)) = true := by
  have h : ((childHH (childLH thetaAboveCell0013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0013)) h
theorem e24KC2ThetaAboveLeaf00132 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0013) = true := by
  have h : ((childHL thetaAboveCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0013) h
theorem e24KC2ThetaAboveLeaf00133 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0013) = true := by
  have h : ((childHH thetaAboveCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0013) h
theorem e24KC2ThetaAboveLeaf0020 :
    adaptiveCoverCheck 15 thetaAboveCell0020 = true := by
  have h : (thetaAboveCell0020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0020 h
theorem e24KC2ThetaAboveLeaf0021 :
    adaptiveCoverCheck 15 thetaAboveCell0021 = true := by
  have h : (thetaAboveCell0021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0021 h
theorem e24KC2ThetaAboveLeaf0022 :
    adaptiveCoverCheck 15 thetaAboveCell0022 = true := by
  have h : (thetaAboveCell0022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0022 h
theorem e24KC2ThetaAboveLeaf0023 :
    adaptiveCoverCheck 15 thetaAboveCell0023 = true := by
  have h : (thetaAboveCell0023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0023 h
theorem e24KC2ThetaAboveLeaf0030 :
    adaptiveCoverCheck 15 thetaAboveCell0030 = true := by
  have h : (thetaAboveCell0030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0030 h
theorem e24KC2ThetaAboveLeaf0031 :
    adaptiveCoverCheck 15 thetaAboveCell0031 = true := by
  have h : (thetaAboveCell0031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0031 h
theorem e24KC2ThetaAboveLeaf0032 :
    adaptiveCoverCheck 15 thetaAboveCell0032 = true := by
  have h : (thetaAboveCell0032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0032 h
theorem e24KC2ThetaAboveLeaf0033 :
    adaptiveCoverCheck 15 thetaAboveCell0033 = true := by
  have h : (thetaAboveCell0033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0033 h
theorem e24KC2ThetaAboveLeaf010000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0100)) = true := by
  have h : ((childLL (childLL thetaAboveCell0100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0100)) h
theorem e24KC2ThetaAboveLeaf010001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0100)) = true := by
  have h : ((childLH (childLL thetaAboveCell0100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0100)) h
theorem e24KC2ThetaAboveLeaf010002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0100)) = true := by
  have h : ((childHL (childLL thetaAboveCell0100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0100)) h
theorem e24KC2ThetaAboveLeaf010003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0100)) = true := by
  have h : ((childHH (childLL thetaAboveCell0100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0100)) h
theorem e24KC2ThetaAboveLeaf010010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0100)) = true := by
  have h : ((childLL (childLH thetaAboveCell0100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0100)) h
theorem e24KC2ThetaAboveLeaf010011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0100)) = true := by
  have h : ((childLH (childLH thetaAboveCell0100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0100)) h
theorem e24KC2ThetaAboveLeaf010012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0100)) = true := by
  have h : ((childHL (childLH thetaAboveCell0100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0100)) h
theorem e24KC2ThetaAboveLeaf010013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0100)) = true := by
  have h : ((childHH (childLH thetaAboveCell0100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0100)) h
theorem e24KC2ThetaAboveLeaf0100200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0100))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0100))) h
theorem e24KC2ThetaAboveLeaf0100201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0100))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0100))) h
theorem e24KC2ThetaAboveLeaf01002020 :
    adaptiveCoverCheck 11 thetaAboveCell01002020 = true := by
  have h : (thetaAboveCell01002020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002020 h
theorem e24KC2ThetaAboveLeaf01002021 :
    adaptiveCoverCheck 11 thetaAboveCell01002021 = true := by
  have h : (thetaAboveCell01002021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002021 h
theorem e24KC2ThetaAboveLeaf01002022 :
    adaptiveCoverCheck 11 thetaAboveCell01002022 = true := by
  have h : (thetaAboveCell01002022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002022 h
theorem e24KC2ThetaAboveLeaf01002023 :
    adaptiveCoverCheck 11 thetaAboveCell01002023 = true := by
  have h : (thetaAboveCell01002023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002023 h
theorem e24KC2ThetaAboveLeaf01002030 :
    adaptiveCoverCheck 11 thetaAboveCell01002030 = true := by
  have h : (thetaAboveCell01002030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002030 h
theorem e24KC2ThetaAboveLeaf01002031 :
    adaptiveCoverCheck 11 thetaAboveCell01002031 = true := by
  have h : (thetaAboveCell01002031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002031 h
theorem e24KC2ThetaAboveLeaf01002032 :
    adaptiveCoverCheck 11 thetaAboveCell01002032 = true := by
  have h : (thetaAboveCell01002032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002032 h
theorem e24KC2ThetaAboveLeaf01002033 :
    adaptiveCoverCheck 11 thetaAboveCell01002033 = true := by
  have h : (thetaAboveCell01002033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002033 h
theorem e24KC2ThetaAboveLeaf0100210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0100))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0100))) h
theorem e24KC2ThetaAboveLeaf0100211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0100))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0100))) h
theorem e24KC2ThetaAboveLeaf01002120 :
    adaptiveCoverCheck 11 thetaAboveCell01002120 = true := by
  have h : (thetaAboveCell01002120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002120 h
theorem e24KC2ThetaAboveLeaf01002121 :
    adaptiveCoverCheck 11 thetaAboveCell01002121 = true := by
  have h : (thetaAboveCell01002121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002121 h
theorem e24KC2ThetaAboveLeaf01002122 :
    adaptiveCoverCheck 11 thetaAboveCell01002122 = true := by
  have h : (thetaAboveCell01002122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002122 h
theorem e24KC2ThetaAboveLeaf01002123 :
    adaptiveCoverCheck 11 thetaAboveCell01002123 = true := by
  have h : (thetaAboveCell01002123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002123 h
theorem e24KC2ThetaAboveLeaf01002130 :
    adaptiveCoverCheck 11 thetaAboveCell01002130 = true := by
  have h : (thetaAboveCell01002130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002130 h
theorem e24KC2ThetaAboveLeaf01002131 :
    adaptiveCoverCheck 11 thetaAboveCell01002131 = true := by
  have h : (thetaAboveCell01002131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002131 h
theorem e24KC2ThetaAboveLeaf01002132 :
    adaptiveCoverCheck 11 thetaAboveCell01002132 = true := by
  have h : (thetaAboveCell01002132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002132 h
theorem e24KC2ThetaAboveLeaf01002133 :
    adaptiveCoverCheck 11 thetaAboveCell01002133 = true := by
  have h : (thetaAboveCell01002133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002133 h
theorem e24KC2ThetaAboveLeaf010022000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01002200) = true := by
  have h : ((childLL thetaAboveCell01002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01002200) h
theorem e24KC2ThetaAboveLeaf010022001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01002200) = true := by
  have h : ((childLH thetaAboveCell01002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01002200) h
theorem e24KC2ThetaAboveLeaf0100220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002200)) h
theorem e24KC2ThetaAboveLeaf0100220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002200)) h
theorem e24KC2ThetaAboveLeaf0100220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002200)) h
theorem e24KC2ThetaAboveLeaf0100220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002200)) h
theorem e24KC2ThetaAboveLeaf010022010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01002201) = true := by
  have h : ((childLL thetaAboveCell01002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01002201) h
theorem e24KC2ThetaAboveLeaf010022011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01002201) = true := by
  have h : ((childLH thetaAboveCell01002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01002201) h
theorem e24KC2ThetaAboveLeaf0100220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002201)) h
theorem e24KC2ThetaAboveLeaf0100220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002201)) h
theorem e24KC2ThetaAboveLeaf0100220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002201)) h
theorem e24KC2ThetaAboveLeaf0100220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002201)) h
theorem e24KC2ThetaAboveLeaf0100220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01002202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01002202)) h
theorem e24KC2ThetaAboveLeaf0100220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01002202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01002202)) h
theorem e24KC2ThetaAboveLeaf010022022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01002202) = true := by
  have h : ((childHL thetaAboveCell01002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01002202) h
theorem e24KC2ThetaAboveLeaf010022023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01002202) = true := by
  have h : ((childHH thetaAboveCell01002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01002202) h
theorem e24KC2ThetaAboveLeaf010022032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01002203) = true := by
  have h : ((childHL thetaAboveCell01002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01002203) h
theorem e24KC2ThetaAboveLeaf010022033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01002203) = true := by
  have h : ((childHH thetaAboveCell01002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01002203) h
theorem e24KC2ThetaAboveLeaf010022100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01002210) = true := by
  have h : ((childLL thetaAboveCell01002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01002210) h
theorem e24KC2ThetaAboveLeaf010022101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01002210) = true := by
  have h : ((childLH thetaAboveCell01002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01002210) h
theorem e24KC2ThetaAboveLeaf0100221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002210)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002210)) h
theorem e24KC2ThetaAboveLeaf0100221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002210)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002210)) h
theorem e24KC2ThetaAboveLeaf0100221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002210)) h
theorem e24KC2ThetaAboveLeaf0100221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002210)) h
theorem e24KC2ThetaAboveLeaf010022110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01002211) = true := by
  have h : ((childLL thetaAboveCell01002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01002211) h
theorem e24KC2ThetaAboveLeaf010022111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01002211) = true := by
  have h : ((childLH thetaAboveCell01002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01002211) h
theorem e24KC2ThetaAboveLeaf0100221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002211)) h
theorem e24KC2ThetaAboveLeaf0100221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002211)) h
theorem e24KC2ThetaAboveLeaf0100221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002211)) h
theorem e24KC2ThetaAboveLeaf0100221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002211)) h
theorem e24KC2ThetaAboveLeaf0100221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01002212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01002212)) h
theorem e24KC2ThetaAboveLeaf0100221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01002212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01002212)) h
theorem e24KC2ThetaAboveLeaf0100221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01002212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01002212)) h
theorem e24KC2ThetaAboveLeaf010022122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01002212) = true := by
  have h : ((childHL thetaAboveCell01002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01002212) h
theorem e24KC2ThetaAboveLeaf010022123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01002212) = true := by
  have h : ((childHH thetaAboveCell01002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01002212) h
theorem e24KC2ThetaAboveLeaf0100221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01002213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01002213)) h
theorem e24KC2ThetaAboveLeaf0100221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01002213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01002213)) h
theorem e24KC2ThetaAboveLeaf0100221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01002213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01002213)) h
theorem e24KC2ThetaAboveLeaf0100221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01002213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01002213)) h
theorem e24KC2ThetaAboveLeaf010022132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01002213) = true := by
  have h : ((childHL thetaAboveCell01002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01002213) h
theorem e24KC2ThetaAboveLeaf010022133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01002213) = true := by
  have h : ((childHH thetaAboveCell01002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01002213) h
theorem e24KC2ThetaAboveLeaf01002220 :
    adaptiveCoverCheck 11 thetaAboveCell01002220 = true := by
  have h : (thetaAboveCell01002220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002220 h
theorem e24KC2ThetaAboveLeaf01002221 :
    adaptiveCoverCheck 11 thetaAboveCell01002221 = true := by
  have h : (thetaAboveCell01002221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002221 h
theorem e24KC2ThetaAboveLeaf01002222 :
    adaptiveCoverCheck 11 thetaAboveCell01002222 = true := by
  have h : (thetaAboveCell01002222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002222 h
theorem e24KC2ThetaAboveLeaf01002223 :
    adaptiveCoverCheck 11 thetaAboveCell01002223 = true := by
  have h : (thetaAboveCell01002223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002223 h
theorem e24KC2ThetaAboveLeaf01002230 :
    adaptiveCoverCheck 11 thetaAboveCell01002230 = true := by
  have h : (thetaAboveCell01002230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002230 h
theorem e24KC2ThetaAboveLeaf01002231 :
    adaptiveCoverCheck 11 thetaAboveCell01002231 = true := by
  have h : (thetaAboveCell01002231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002231 h
theorem e24KC2ThetaAboveLeaf01002232 :
    adaptiveCoverCheck 11 thetaAboveCell01002232 = true := by
  have h : (thetaAboveCell01002232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002232 h
theorem e24KC2ThetaAboveLeaf01002233 :
    adaptiveCoverCheck 11 thetaAboveCell01002233 = true := by
  have h : (thetaAboveCell01002233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002233 h
theorem e24KC2ThetaAboveLeaf010023000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01002300) = true := by
  have h : ((childLL thetaAboveCell01002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01002300) h
theorem e24KC2ThetaAboveLeaf010023001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01002300) = true := by
  have h : ((childLH thetaAboveCell01002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01002300) h
theorem e24KC2ThetaAboveLeaf0100230020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002300)) h
theorem e24KC2ThetaAboveLeaf0100230021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002300)) h
theorem e24KC2ThetaAboveLeaf0100230030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002300)) h
theorem e24KC2ThetaAboveLeaf0100230031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002300)) h
theorem e24KC2ThetaAboveLeaf010023010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01002301) = true := by
  have h : ((childLL thetaAboveCell01002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01002301) h
theorem e24KC2ThetaAboveLeaf010023011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01002301) = true := by
  have h : ((childLH thetaAboveCell01002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01002301) h
theorem e24KC2ThetaAboveLeaf0100230120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002301)) h
theorem e24KC2ThetaAboveLeaf0100230121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002301)) h
theorem e24KC2ThetaAboveLeaf0100230130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002301)) h
theorem e24KC2ThetaAboveLeaf0100230131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002301)) h
theorem e24KC2ThetaAboveLeaf0100230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01002302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01002302)) h
theorem e24KC2ThetaAboveLeaf0100230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01002302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01002302)) h
theorem e24KC2ThetaAboveLeaf0100230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01002302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01002302)) h
theorem e24KC2ThetaAboveLeaf0100230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01002302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01002302)) h
theorem e24KC2ThetaAboveLeaf010023022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01002302) = true := by
  have h : ((childHL thetaAboveCell01002302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01002302) h
theorem e24KC2ThetaAboveLeaf010023023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01002302) = true := by
  have h : ((childHH thetaAboveCell01002302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01002302) h
theorem e24KC2ThetaAboveLeaf0100230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01002303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01002303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01002303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01002303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf0100230333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01002303)) h
theorem e24KC2ThetaAboveLeaf010023100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01002310) = true := by
  have h : ((childLL thetaAboveCell01002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01002310) h
theorem e24KC2ThetaAboveLeaf010023101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01002310) = true := by
  have h : ((childLH thetaAboveCell01002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01002310) h
theorem e24KC2ThetaAboveLeaf0100231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002310)) h
theorem e24KC2ThetaAboveLeaf0100231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002310)) h
theorem e24KC2ThetaAboveLeaf0100231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002310)) h
theorem e24KC2ThetaAboveLeaf0100231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002310)) h
theorem e24KC2ThetaAboveLeaf010023110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01002311) = true := by
  have h : ((childLL thetaAboveCell01002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01002311) h
theorem e24KC2ThetaAboveLeaf010023111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01002311) = true := by
  have h : ((childLH thetaAboveCell01002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01002311) h
theorem e24KC2ThetaAboveLeaf0100231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002311)) h
theorem e24KC2ThetaAboveLeaf0100231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002311)) h
theorem e24KC2ThetaAboveLeaf0100231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002311)) h
theorem e24KC2ThetaAboveLeaf0100231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002311)) h
theorem e24KC2ThetaAboveLeaf0100231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01002312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01002312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01002312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01002312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01002312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01002312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01002312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01002312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01002312)) h
theorem e24KC2ThetaAboveLeaf0100231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01002313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01002313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01002313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01002313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01002313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01002313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01002313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01002313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01002313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01002313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01002313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01002313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf0100231333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01002313)) h
theorem e24KC2ThetaAboveLeaf01002320 :
    adaptiveCoverCheck 11 thetaAboveCell01002320 = true := by
  have h : (thetaAboveCell01002320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002320 h
theorem e24KC2ThetaAboveLeaf01002321 :
    adaptiveCoverCheck 11 thetaAboveCell01002321 = true := by
  have h : (thetaAboveCell01002321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002321 h
theorem e24KC2ThetaAboveLeaf01002322 :
    adaptiveCoverCheck 11 thetaAboveCell01002322 = true := by
  have h : (thetaAboveCell01002322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002322 h
theorem e24KC2ThetaAboveLeaf01002323 :
    adaptiveCoverCheck 11 thetaAboveCell01002323 = true := by
  have h : (thetaAboveCell01002323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002323 h
theorem e24KC2ThetaAboveLeaf01002330 :
    adaptiveCoverCheck 11 thetaAboveCell01002330 = true := by
  have h : (thetaAboveCell01002330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002330 h
theorem e24KC2ThetaAboveLeaf01002331 :
    adaptiveCoverCheck 11 thetaAboveCell01002331 = true := by
  have h : (thetaAboveCell01002331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002331 h
theorem e24KC2ThetaAboveLeaf01002332 :
    adaptiveCoverCheck 11 thetaAboveCell01002332 = true := by
  have h : (thetaAboveCell01002332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002332 h
theorem e24KC2ThetaAboveLeaf01002333 :
    adaptiveCoverCheck 11 thetaAboveCell01002333 = true := by
  have h : (thetaAboveCell01002333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01002333 h
theorem e24KC2ThetaAboveLeaf0100300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0100))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0100))) h
theorem e24KC2ThetaAboveLeaf0100301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0100))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0100))) h
theorem e24KC2ThetaAboveLeaf01003020 :
    adaptiveCoverCheck 11 thetaAboveCell01003020 = true := by
  have h : (thetaAboveCell01003020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003020 h
theorem e24KC2ThetaAboveLeaf01003021 :
    adaptiveCoverCheck 11 thetaAboveCell01003021 = true := by
  have h : (thetaAboveCell01003021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003021 h
theorem e24KC2ThetaAboveLeaf01003022 :
    adaptiveCoverCheck 11 thetaAboveCell01003022 = true := by
  have h : (thetaAboveCell01003022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003022 h
theorem e24KC2ThetaAboveLeaf01003023 :
    adaptiveCoverCheck 11 thetaAboveCell01003023 = true := by
  have h : (thetaAboveCell01003023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003023 h
theorem e24KC2ThetaAboveLeaf01003030 :
    adaptiveCoverCheck 11 thetaAboveCell01003030 = true := by
  have h : (thetaAboveCell01003030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003030 h
theorem e24KC2ThetaAboveLeaf01003031 :
    adaptiveCoverCheck 11 thetaAboveCell01003031 = true := by
  have h : (thetaAboveCell01003031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003031 h
theorem e24KC2ThetaAboveLeaf01003032 :
    adaptiveCoverCheck 11 thetaAboveCell01003032 = true := by
  have h : (thetaAboveCell01003032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003032 h
theorem e24KC2ThetaAboveLeaf01003033 :
    adaptiveCoverCheck 11 thetaAboveCell01003033 = true := by
  have h : (thetaAboveCell01003033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003033 h
theorem e24KC2ThetaAboveLeaf0100310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0100))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0100))) h
theorem e24KC2ThetaAboveLeaf0100311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0100))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0100))) h
theorem e24KC2ThetaAboveLeaf01003120 :
    adaptiveCoverCheck 11 thetaAboveCell01003120 = true := by
  have h : (thetaAboveCell01003120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003120 h
theorem e24KC2ThetaAboveLeaf01003121 :
    adaptiveCoverCheck 11 thetaAboveCell01003121 = true := by
  have h : (thetaAboveCell01003121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003121 h
theorem e24KC2ThetaAboveLeaf01003122 :
    adaptiveCoverCheck 11 thetaAboveCell01003122 = true := by
  have h : (thetaAboveCell01003122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003122 h
theorem e24KC2ThetaAboveLeaf01003123 :
    adaptiveCoverCheck 11 thetaAboveCell01003123 = true := by
  have h : (thetaAboveCell01003123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003123 h
theorem e24KC2ThetaAboveLeaf01003130 :
    adaptiveCoverCheck 11 thetaAboveCell01003130 = true := by
  have h : (thetaAboveCell01003130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003130 h
theorem e24KC2ThetaAboveLeaf01003131 :
    adaptiveCoverCheck 11 thetaAboveCell01003131 = true := by
  have h : (thetaAboveCell01003131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003131 h
theorem e24KC2ThetaAboveLeaf01003132 :
    adaptiveCoverCheck 11 thetaAboveCell01003132 = true := by
  have h : (thetaAboveCell01003132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003132 h
theorem e24KC2ThetaAboveLeaf01003133 :
    adaptiveCoverCheck 11 thetaAboveCell01003133 = true := by
  have h : (thetaAboveCell01003133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003133 h
theorem e24KC2ThetaAboveLeaf010032000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003200) = true := by
  have h : ((childLL thetaAboveCell01003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003200) h
theorem e24KC2ThetaAboveLeaf010032001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003200) = true := by
  have h : ((childLH thetaAboveCell01003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003200) h
theorem e24KC2ThetaAboveLeaf0100320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003200)) h
theorem e24KC2ThetaAboveLeaf0100320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003200)) h
theorem e24KC2ThetaAboveLeaf0100320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003200)) h
theorem e24KC2ThetaAboveLeaf0100320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003200)) h
theorem e24KC2ThetaAboveLeaf010032010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003201) = true := by
  have h : ((childLL thetaAboveCell01003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003201) h
theorem e24KC2ThetaAboveLeaf010032011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003201) = true := by
  have h : ((childLH thetaAboveCell01003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003201) h
theorem e24KC2ThetaAboveLeaf0100320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003201)) h
theorem e24KC2ThetaAboveLeaf0100320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003201)) h
theorem e24KC2ThetaAboveLeaf0100320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003201)) h
theorem e24KC2ThetaAboveLeaf0100320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003201)) h
theorem e24KC2ThetaAboveLeaf0100320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01003202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01003202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01003202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01003202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01003202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01003202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01003202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01003202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003202)) h
theorem e24KC2ThetaAboveLeaf0100320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01003203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01003203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01003203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01003203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01003203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01003203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01003203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01003203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf0100320333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003203)) h
theorem e24KC2ThetaAboveLeaf010032100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003210) = true := by
  have h : ((childLL thetaAboveCell01003210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003210) h
theorem e24KC2ThetaAboveLeaf010032101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003210) = true := by
  have h : ((childLH thetaAboveCell01003210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003210) h
theorem e24KC2ThetaAboveLeaf0100321020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003210)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003210)) h
theorem e24KC2ThetaAboveLeaf0100321021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003210)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003210)) h
theorem e24KC2ThetaAboveLeaf0100321022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003210)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003210)) h
theorem e24KC2ThetaAboveLeaf0100321023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003210)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003210)) h
theorem e24KC2ThetaAboveLeaf0100321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003210)) h
theorem e24KC2ThetaAboveLeaf0100321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003210)) h
theorem e24KC2ThetaAboveLeaf0100321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003210)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003210)) h
theorem e24KC2ThetaAboveLeaf0100321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003210)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003210)) h
theorem e24KC2ThetaAboveLeaf010032110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003211) = true := by
  have h : ((childLL thetaAboveCell01003211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003211) h
theorem e24KC2ThetaAboveLeaf010032111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003211) = true := by
  have h : ((childLH thetaAboveCell01003211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003211) h
theorem e24KC2ThetaAboveLeaf0100321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003211)) h
theorem e24KC2ThetaAboveLeaf0100321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003211)) h
theorem e24KC2ThetaAboveLeaf0100321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003211)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003211)) h
theorem e24KC2ThetaAboveLeaf0100321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003211)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003211)) h
theorem e24KC2ThetaAboveLeaf0100321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003211)) h
theorem e24KC2ThetaAboveLeaf0100321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003211)) h
theorem e24KC2ThetaAboveLeaf0100321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003211)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003211)) h
theorem e24KC2ThetaAboveLeaf0100321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003211)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003211)) h
theorem e24KC2ThetaAboveLeaf0100321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01003212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01003212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01003212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01003212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01003212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01003212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01003212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01003212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003212)) h
theorem e24KC2ThetaAboveLeaf0100321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01003213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01003213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01003213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01003213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01003213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01003213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01003213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01003213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf0100321333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003213)) h
theorem e24KC2ThetaAboveLeaf01003220 :
    adaptiveCoverCheck 11 thetaAboveCell01003220 = true := by
  have h : (thetaAboveCell01003220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003220 h
theorem e24KC2ThetaAboveLeaf01003221 :
    adaptiveCoverCheck 11 thetaAboveCell01003221 = true := by
  have h : (thetaAboveCell01003221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003221 h
theorem e24KC2ThetaAboveLeaf01003222 :
    adaptiveCoverCheck 11 thetaAboveCell01003222 = true := by
  have h : (thetaAboveCell01003222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003222 h
theorem e24KC2ThetaAboveLeaf01003223 :
    adaptiveCoverCheck 11 thetaAboveCell01003223 = true := by
  have h : (thetaAboveCell01003223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003223 h
theorem e24KC2ThetaAboveLeaf01003230 :
    adaptiveCoverCheck 11 thetaAboveCell01003230 = true := by
  have h : (thetaAboveCell01003230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003230 h
theorem e24KC2ThetaAboveLeaf01003231 :
    adaptiveCoverCheck 11 thetaAboveCell01003231 = true := by
  have h : (thetaAboveCell01003231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003231 h
theorem e24KC2ThetaAboveLeaf01003232 :
    adaptiveCoverCheck 11 thetaAboveCell01003232 = true := by
  have h : (thetaAboveCell01003232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003232 h
theorem e24KC2ThetaAboveLeaf01003233 :
    adaptiveCoverCheck 11 thetaAboveCell01003233 = true := by
  have h : (thetaAboveCell01003233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01003233 h
theorem e24KC2ThetaAboveLeaf010033000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003300) = true := by
  have h : ((childLL thetaAboveCell01003300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003300) h
theorem e24KC2ThetaAboveLeaf010033001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003300) = true := by
  have h : ((childLH thetaAboveCell01003300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003300) h
theorem e24KC2ThetaAboveLeaf0100330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003300)) h
theorem e24KC2ThetaAboveLeaf0100330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003300)) h
theorem e24KC2ThetaAboveLeaf0100330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003300)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003300)) h
theorem e24KC2ThetaAboveLeaf0100330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003300)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003300)) h
theorem e24KC2ThetaAboveLeaf0100330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003300)) h
theorem e24KC2ThetaAboveLeaf0100330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003300)) h
theorem e24KC2ThetaAboveLeaf0100330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003300)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003300)) h
theorem e24KC2ThetaAboveLeaf0100330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003300)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003300)) h
theorem e24KC2ThetaAboveLeaf010033010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01003301) = true := by
  have h : ((childLL thetaAboveCell01003301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01003301) h
theorem e24KC2ThetaAboveLeaf010033011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01003301) = true := by
  have h : ((childLH thetaAboveCell01003301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01003301) h
theorem e24KC2ThetaAboveLeaf0100330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003301)) h
theorem e24KC2ThetaAboveLeaf0100330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003301)) h
theorem e24KC2ThetaAboveLeaf0100330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003301)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003301)) h
theorem e24KC2ThetaAboveLeaf0100330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003301)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003301)) h
theorem e24KC2ThetaAboveLeaf0100330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003301)) h
theorem e24KC2ThetaAboveLeaf0100330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003301)) h
theorem e24KC2ThetaAboveLeaf0100330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003301)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003301)) h
theorem e24KC2ThetaAboveLeaf0100330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003301)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003301)) h
theorem e24KC2ThetaAboveLeaf0100330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01003302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01003302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01003302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01003302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01003302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01003302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01003302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01003302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01003302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01003302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01003302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01003302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01003302)) h
theorem e24KC2ThetaAboveLeaf0100330233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01003302)) h

end PartE
end GerverSofa

end

end

end
