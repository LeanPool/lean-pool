/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT358400010`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse8870ef6ec

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0112 : AngleCell :=
  childHL (childLH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0113 : AngleCell :=
  childHH (childLH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0120 : AngleCell :=
  childLL (childHL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0121 : AngleCell :=
  childLH (childHL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0122 : AngleCell :=
  childHL (childHL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0123 : AngleCell :=
  childHH (childHL (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0130 : AngleCell :=
  childLL (childHH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0131 : AngleCell :=
  childLH (childHH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0132 : AngleCell :=
  childHL (childHH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0133 : AngleCell :=
  childHH (childHH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `1000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `01113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0111)))
/-- Subcell `01113333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0111)))
/-- Subcell `10002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell1000)))
/-- Subcell `10002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell1000)))
/-- Subcell `10002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell1000)))
/-- Subcell `10002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell1000)))
/-- Subcell `10002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell1000)))
/-- Subcell `10002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell1000)))
/-- Subcell `10002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell1000)))
/-- Subcell `10002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell1000)))
/-- Subcell `10002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell1000)))
/-- Subcell `10002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell1000)))
/-- Subcell `10002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell1000)))
/-- Subcell `10002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell1000)))
/-- Subcell `10002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell1000)))
/-- Subcell `10002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell1000)))
/-- Subcell `10002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell1000)))
/-- Subcell `10002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell1000)))
/-- Subcell `10002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1000)))
/-- Subcell `10002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10002333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1000)))
/-- Subcell `10003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell1000)))
/-- Subcell `10003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell1000)))
/-- Subcell `10003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell1000)))
/-- Subcell `10003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell1000)))
/-- Subcell `10003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell1000)))
/-- Subcell `10003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell1000)))
/-- Subcell `10003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell1000)))
/-- Subcell `10003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell1000)))
/-- Subcell `10003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell1000)))
/-- Subcell `10003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell1000)))
/-- Subcell `10003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell1000)))
/-- Subcell `10003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell1000)))
/-- Subcell `10003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell1000)))
/-- Subcell `10003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell1000)))
/-- Subcell `10003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell1000)))
/-- Subcell `10003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell1000)))
/-- Subcell `10003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1000)))
/-- Subcell `10003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1000)))
/-- Subcell `10003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1000)))

end CertificateCellse8870ef6ec

open CertificateCellse8870ef6ec
theorem e24KC2ThetaAboveLeaf0111320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf011132100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113210) = true := by
  have h : ((childLL thetaAboveCell01113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113210) h
theorem e24KC2ThetaAboveLeaf011132101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113210) = true := by
  have h : ((childLH thetaAboveCell01113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113210) h
theorem e24KC2ThetaAboveLeaf011132102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113210) = true := by
  have h : ((childHL thetaAboveCell01113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113210) h
theorem e24KC2ThetaAboveLeaf011132103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113210) = true := by
  have h : ((childHH thetaAboveCell01113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113210) h
theorem e24KC2ThetaAboveLeaf011132110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113211) = true := by
  have h : ((childLL thetaAboveCell01113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113211) h
theorem e24KC2ThetaAboveLeaf011132111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113211) = true := by
  have h : ((childLH thetaAboveCell01113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113211) h
theorem e24KC2ThetaAboveLeaf011132112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113211) = true := by
  have h : ((childHL thetaAboveCell01113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113211) h
theorem e24KC2ThetaAboveLeaf011132113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113211) = true := by
  have h : ((childHH thetaAboveCell01113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113211) h
theorem e24KC2ThetaAboveLeaf0111321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf011132200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113220) = true := by
  have h : ((childLL thetaAboveCell01113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113220) h
theorem e24KC2ThetaAboveLeaf011132201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113220) = true := by
  have h : ((childLH thetaAboveCell01113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113220) h
theorem e24KC2ThetaAboveLeaf011132202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113220) = true := by
  have h : ((childHL thetaAboveCell01113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113220) h
theorem e24KC2ThetaAboveLeaf011132203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113220) = true := by
  have h : ((childHH thetaAboveCell01113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113220) h
theorem e24KC2ThetaAboveLeaf011132210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113221) = true := by
  have h : ((childLL thetaAboveCell01113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113221) h
theorem e24KC2ThetaAboveLeaf011132211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113221) = true := by
  have h : ((childLH thetaAboveCell01113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113221) h
theorem e24KC2ThetaAboveLeaf011132212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113221) = true := by
  have h : ((childHL thetaAboveCell01113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113221) h
theorem e24KC2ThetaAboveLeaf011132213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113221) = true := by
  have h : ((childHH thetaAboveCell01113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113221) h
theorem e24KC2ThetaAboveLeaf01113222 :
    adaptiveCoverCheck 11 thetaAboveCell01113222 = true := by
  have h : (thetaAboveCell01113222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113222 h
theorem e24KC2ThetaAboveLeaf01113223 :
    adaptiveCoverCheck 11 thetaAboveCell01113223 = true := by
  have h : (thetaAboveCell01113223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113223 h
theorem e24KC2ThetaAboveLeaf011132300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113230) = true := by
  have h : ((childLL thetaAboveCell01113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113230) h
theorem e24KC2ThetaAboveLeaf011132301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113230) = true := by
  have h : ((childLH thetaAboveCell01113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113230) h
theorem e24KC2ThetaAboveLeaf011132302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113230) = true := by
  have h : ((childHL thetaAboveCell01113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113230) h
theorem e24KC2ThetaAboveLeaf011132303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113230) = true := by
  have h : ((childHH thetaAboveCell01113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113230) h
theorem e24KC2ThetaAboveLeaf011132310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113231) = true := by
  have h : ((childLL thetaAboveCell01113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113231) h
theorem e24KC2ThetaAboveLeaf011132311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113231) = true := by
  have h : ((childLH thetaAboveCell01113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113231) h
theorem e24KC2ThetaAboveLeaf011132312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113231) = true := by
  have h : ((childHL thetaAboveCell01113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113231) h
theorem e24KC2ThetaAboveLeaf011132313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113231) = true := by
  have h : ((childHH thetaAboveCell01113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113231) h
theorem e24KC2ThetaAboveLeaf01113232 :
    adaptiveCoverCheck 11 thetaAboveCell01113232 = true := by
  have h : (thetaAboveCell01113232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113232 h
theorem e24KC2ThetaAboveLeaf01113233 :
    adaptiveCoverCheck 11 thetaAboveCell01113233 = true := by
  have h : (thetaAboveCell01113233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113233 h
theorem e24KC2ThetaAboveLeaf011133000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113300) = true := by
  have h : ((childLL thetaAboveCell01113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113300) h
theorem e24KC2ThetaAboveLeaf011133001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113300) = true := by
  have h : ((childLH thetaAboveCell01113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113300) h
theorem e24KC2ThetaAboveLeaf011133002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113300) = true := by
  have h : ((childHL thetaAboveCell01113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113300) h
theorem e24KC2ThetaAboveLeaf011133003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113300) = true := by
  have h : ((childHH thetaAboveCell01113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113300) h
theorem e24KC2ThetaAboveLeaf011133010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113301) = true := by
  have h : ((childLL thetaAboveCell01113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113301) h
theorem e24KC2ThetaAboveLeaf011133011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113301) = true := by
  have h : ((childLH thetaAboveCell01113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113301) h
theorem e24KC2ThetaAboveLeaf011133012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113301) = true := by
  have h : ((childHL thetaAboveCell01113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113301) h
theorem e24KC2ThetaAboveLeaf011133013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113301) = true := by
  have h : ((childHH thetaAboveCell01113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113301) h
theorem e24KC2ThetaAboveLeaf0111330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf011133100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113310) = true := by
  have h : ((childLL thetaAboveCell01113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113310) h
theorem e24KC2ThetaAboveLeaf011133101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113310) = true := by
  have h : ((childLH thetaAboveCell01113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113310) h
theorem e24KC2ThetaAboveLeaf011133102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113310) = true := by
  have h : ((childHL thetaAboveCell01113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113310) h
theorem e24KC2ThetaAboveLeaf011133103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113310) = true := by
  have h : ((childHH thetaAboveCell01113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113310) h
theorem e24KC2ThetaAboveLeaf011133110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113311) = true := by
  have h : ((childLL thetaAboveCell01113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113311) h
theorem e24KC2ThetaAboveLeaf011133111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113311) = true := by
  have h : ((childLH thetaAboveCell01113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113311) h
theorem e24KC2ThetaAboveLeaf011133112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113311) = true := by
  have h : ((childHL thetaAboveCell01113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113311) h
theorem e24KC2ThetaAboveLeaf011133113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113311) = true := by
  have h : ((childHH thetaAboveCell01113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113311) h
theorem e24KC2ThetaAboveLeaf0111331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf011133200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113320) = true := by
  have h : ((childLL thetaAboveCell01113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113320) h
theorem e24KC2ThetaAboveLeaf011133201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113320) = true := by
  have h : ((childLH thetaAboveCell01113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113320) h
theorem e24KC2ThetaAboveLeaf011133202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113320) = true := by
  have h : ((childHL thetaAboveCell01113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113320) h
theorem e24KC2ThetaAboveLeaf011133203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113320) = true := by
  have h : ((childHH thetaAboveCell01113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113320) h
theorem e24KC2ThetaAboveLeaf011133210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113321) = true := by
  have h : ((childLL thetaAboveCell01113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113321) h
theorem e24KC2ThetaAboveLeaf011133211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113321) = true := by
  have h : ((childLH thetaAboveCell01113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113321) h
theorem e24KC2ThetaAboveLeaf011133212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113321) = true := by
  have h : ((childHL thetaAboveCell01113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113321) h
theorem e24KC2ThetaAboveLeaf011133213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113321) = true := by
  have h : ((childHH thetaAboveCell01113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113321) h
theorem e24KC2ThetaAboveLeaf01113322 :
    adaptiveCoverCheck 11 thetaAboveCell01113322 = true := by
  have h : (thetaAboveCell01113322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113322 h
theorem e24KC2ThetaAboveLeaf01113323 :
    adaptiveCoverCheck 11 thetaAboveCell01113323 = true := by
  have h : (thetaAboveCell01113323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113323 h
theorem e24KC2ThetaAboveLeaf011133300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113330) = true := by
  have h : ((childLL thetaAboveCell01113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113330) h
theorem e24KC2ThetaAboveLeaf011133301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113330) = true := by
  have h : ((childLH thetaAboveCell01113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113330) h
theorem e24KC2ThetaAboveLeaf011133302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113330) = true := by
  have h : ((childHL thetaAboveCell01113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113330) h
theorem e24KC2ThetaAboveLeaf011133303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113330) = true := by
  have h : ((childHH thetaAboveCell01113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113330) h
theorem e24KC2ThetaAboveLeaf011133310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113331) = true := by
  have h : ((childLL thetaAboveCell01113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113331) h
theorem e24KC2ThetaAboveLeaf011133311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113331) = true := by
  have h : ((childLH thetaAboveCell01113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113331) h
theorem e24KC2ThetaAboveLeaf011133312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113331) = true := by
  have h : ((childHL thetaAboveCell01113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113331) h
theorem e24KC2ThetaAboveLeaf011133313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113331) = true := by
  have h : ((childHH thetaAboveCell01113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113331) h
theorem e24KC2ThetaAboveLeaf01113332 :
    adaptiveCoverCheck 11 thetaAboveCell01113332 = true := by
  have h : (thetaAboveCell01113332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113332 h
theorem e24KC2ThetaAboveLeaf01113333 :
    adaptiveCoverCheck 11 thetaAboveCell01113333 = true := by
  have h : (thetaAboveCell01113333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113333 h
theorem e24KC2ThetaAboveLeaf0112000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0112))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0112))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0112))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0112))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0112))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0112))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0112))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0112))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf011202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0112)) = true := by
  have h : ((childHL (childLL thetaAboveCell0112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0112)) h
theorem e24KC2ThetaAboveLeaf011203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0112)) = true := by
  have h : ((childHH (childLL thetaAboveCell0112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0112)) h
theorem e24KC2ThetaAboveLeaf0112100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0112))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0112))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0112))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0112))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0112))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0112))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0112))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0112))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf011212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0112)) = true := by
  have h : ((childHL (childLH thetaAboveCell0112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0112)) h
theorem e24KC2ThetaAboveLeaf011213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0112)) = true := by
  have h : ((childHH (childLH thetaAboveCell0112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0112)) h
theorem e24KC2ThetaAboveLeaf01122 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0112) = true := by
  have h : ((childHL thetaAboveCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0112) h
theorem e24KC2ThetaAboveLeaf01123 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0112) = true := by
  have h : ((childHH thetaAboveCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0112) h
theorem e24KC2ThetaAboveLeaf0113000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0113))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0113))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0113))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0113))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0113))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0113))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0113))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0113))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf011302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0113)) = true := by
  have h : ((childHL (childLL thetaAboveCell0113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0113)) h
theorem e24KC2ThetaAboveLeaf011303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0113)) = true := by
  have h : ((childHH (childLL thetaAboveCell0113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0113)) h
theorem e24KC2ThetaAboveLeaf0113100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0113))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0113))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0113))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0113))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0113))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0113))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0113))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0113))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf011312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0113)) = true := by
  have h : ((childHL (childLH thetaAboveCell0113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0113)) h
theorem e24KC2ThetaAboveLeaf011313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0113)) = true := by
  have h : ((childHH (childLH thetaAboveCell0113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0113)) h
theorem e24KC2ThetaAboveLeaf01132 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0113) = true := by
  have h : ((childHL thetaAboveCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0113) h
theorem e24KC2ThetaAboveLeaf01133 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0113) = true := by
  have h : ((childHH thetaAboveCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0113) h
theorem e24KC2ThetaAboveLeaf0120 :
    adaptiveCoverCheck 15 thetaAboveCell0120 = true := by
  have h : (thetaAboveCell0120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0120 h
theorem e24KC2ThetaAboveLeaf0121 :
    adaptiveCoverCheck 15 thetaAboveCell0121 = true := by
  have h : (thetaAboveCell0121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0121 h
theorem e24KC2ThetaAboveLeaf0122 :
    adaptiveCoverCheck 15 thetaAboveCell0122 = true := by
  have h : (thetaAboveCell0122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0122 h
theorem e24KC2ThetaAboveLeaf0123 :
    adaptiveCoverCheck 15 thetaAboveCell0123 = true := by
  have h : (thetaAboveCell0123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0123 h
theorem e24KC2ThetaAboveLeaf0130 :
    adaptiveCoverCheck 15 thetaAboveCell0130 = true := by
  have h : (thetaAboveCell0130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0130 h
theorem e24KC2ThetaAboveLeaf0131 :
    adaptiveCoverCheck 15 thetaAboveCell0131 = true := by
  have h : (thetaAboveCell0131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0131 h
theorem e24KC2ThetaAboveLeaf0132 :
    adaptiveCoverCheck 15 thetaAboveCell0132 = true := by
  have h : (thetaAboveCell0132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0132 h
theorem e24KC2ThetaAboveLeaf0133 :
    adaptiveCoverCheck 15 thetaAboveCell0133 = true := by
  have h : (thetaAboveCell0133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0133 h
theorem e24KC2ThetaAboveLeaf020 :
    adaptiveCoverCheck 16 (childLL (childHL (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf021 :
    adaptiveCoverCheck 16 (childLH (childHL (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf022 :
    adaptiveCoverCheck 16 (childHL (childHL (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHL (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHL (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf023 :
    adaptiveCoverCheck 16 (childHH (childHL (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf030 :
    adaptiveCoverCheck 16 (childLL (childHH (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf031 :
    adaptiveCoverCheck 16 (childLH (childHH (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf032 :
    adaptiveCoverCheck 16 (childHL (childHH (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf033 :
    adaptiveCoverCheck 16 (childHH (childHH (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf100000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1000)) = true := by
  have h : ((childLL (childLL thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1000)) = true := by
  have h : ((childLH (childLL thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1000)) = true := by
  have h : ((childHL (childLL thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1000)) = true := by
  have h : ((childHH (childLL thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1000)) = true := by
  have h : ((childLL (childLH thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1000)) = true := by
  have h : ((childLH (childLH thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1000)) = true := by
  have h : ((childHL (childLH thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1000)) = true := by
  have h : ((childHH (childLH thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf1000200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1000))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf1000201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1000))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf10002020 :
    adaptiveCoverCheck 11 thetaAboveCell10002020 = true := by
  have h : (thetaAboveCell10002020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002020 h
theorem e24KC2ThetaAboveLeaf10002021 :
    adaptiveCoverCheck 11 thetaAboveCell10002021 = true := by
  have h : (thetaAboveCell10002021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002021 h
theorem e24KC2ThetaAboveLeaf10002022 :
    adaptiveCoverCheck 11 thetaAboveCell10002022 = true := by
  have h : (thetaAboveCell10002022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002022 h
theorem e24KC2ThetaAboveLeaf10002023 :
    adaptiveCoverCheck 11 thetaAboveCell10002023 = true := by
  have h : (thetaAboveCell10002023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002023 h
theorem e24KC2ThetaAboveLeaf10002030 :
    adaptiveCoverCheck 11 thetaAboveCell10002030 = true := by
  have h : (thetaAboveCell10002030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002030 h
theorem e24KC2ThetaAboveLeaf10002031 :
    adaptiveCoverCheck 11 thetaAboveCell10002031 = true := by
  have h : (thetaAboveCell10002031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002031 h
theorem e24KC2ThetaAboveLeaf10002032 :
    adaptiveCoverCheck 11 thetaAboveCell10002032 = true := by
  have h : (thetaAboveCell10002032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002032 h
theorem e24KC2ThetaAboveLeaf10002033 :
    adaptiveCoverCheck 11 thetaAboveCell10002033 = true := by
  have h : (thetaAboveCell10002033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002033 h
theorem e24KC2ThetaAboveLeaf1000210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1000))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf1000211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1000))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf10002120 :
    adaptiveCoverCheck 11 thetaAboveCell10002120 = true := by
  have h : (thetaAboveCell10002120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002120 h
theorem e24KC2ThetaAboveLeaf10002121 :
    adaptiveCoverCheck 11 thetaAboveCell10002121 = true := by
  have h : (thetaAboveCell10002121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002121 h
theorem e24KC2ThetaAboveLeaf10002122 :
    adaptiveCoverCheck 11 thetaAboveCell10002122 = true := by
  have h : (thetaAboveCell10002122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002122 h
theorem e24KC2ThetaAboveLeaf10002123 :
    adaptiveCoverCheck 11 thetaAboveCell10002123 = true := by
  have h : (thetaAboveCell10002123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002123 h
theorem e24KC2ThetaAboveLeaf10002130 :
    adaptiveCoverCheck 11 thetaAboveCell10002130 = true := by
  have h : (thetaAboveCell10002130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002130 h
theorem e24KC2ThetaAboveLeaf10002131 :
    adaptiveCoverCheck 11 thetaAboveCell10002131 = true := by
  have h : (thetaAboveCell10002131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002131 h
theorem e24KC2ThetaAboveLeaf10002132 :
    adaptiveCoverCheck 11 thetaAboveCell10002132 = true := by
  have h : (thetaAboveCell10002132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002132 h
theorem e24KC2ThetaAboveLeaf10002133 :
    adaptiveCoverCheck 11 thetaAboveCell10002133 = true := by
  have h : (thetaAboveCell10002133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002133 h
theorem e24KC2ThetaAboveLeaf100022000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002200) = true := by
  have h : ((childLL thetaAboveCell10002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002200) h
theorem e24KC2ThetaAboveLeaf100022001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002200) = true := by
  have h : ((childLH thetaAboveCell10002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002200) h
theorem e24KC2ThetaAboveLeaf100022002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002200) = true := by
  have h : ((childHL thetaAboveCell10002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002200) h
theorem e24KC2ThetaAboveLeaf100022003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002200) = true := by
  have h : ((childHH thetaAboveCell10002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002200) h
theorem e24KC2ThetaAboveLeaf100022010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002201) = true := by
  have h : ((childLL thetaAboveCell10002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002201) h
theorem e24KC2ThetaAboveLeaf100022011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002201) = true := by
  have h : ((childLH thetaAboveCell10002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002201) h
theorem e24KC2ThetaAboveLeaf100022012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002201) = true := by
  have h : ((childHL thetaAboveCell10002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002201) h
theorem e24KC2ThetaAboveLeaf100022013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002201) = true := by
  have h : ((childHH thetaAboveCell10002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002201) h
theorem e24KC2ThetaAboveLeaf1000220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002202)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002202)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002202)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002202)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002202)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002202)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002202)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002202)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002202)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002202)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002202)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002202)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002202)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002202)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002202)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002202)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002203)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002203)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002203)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002203)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002203)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002203)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002203)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002203)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002203)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002203)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002203)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002203)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002203)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002203)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002203)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002203)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf100022100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002210) = true := by
  have h : ((childLL thetaAboveCell10002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002210) h
theorem e24KC2ThetaAboveLeaf100022101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002210) = true := by
  have h : ((childLH thetaAboveCell10002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002210) h
theorem e24KC2ThetaAboveLeaf100022102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002210) = true := by
  have h : ((childHL thetaAboveCell10002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002210) h
theorem e24KC2ThetaAboveLeaf100022103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002210) = true := by
  have h : ((childHH thetaAboveCell10002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002210) h
theorem e24KC2ThetaAboveLeaf100022110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002211) = true := by
  have h : ((childLL thetaAboveCell10002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002211) h
theorem e24KC2ThetaAboveLeaf100022111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002211) = true := by
  have h : ((childLH thetaAboveCell10002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002211) h
theorem e24KC2ThetaAboveLeaf100022112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002211) = true := by
  have h : ((childHL thetaAboveCell10002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002211) h
theorem e24KC2ThetaAboveLeaf100022113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002211) = true := by
  have h : ((childHH thetaAboveCell10002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002211) h
theorem e24KC2ThetaAboveLeaf1000221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002212)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002212)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002212)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002212)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002212)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002212)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002212)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002212)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002212)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002212)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002212)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002212)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002212)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002212)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002212)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002212)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002213)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002213)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002213)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002213)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002213)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002213)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002213)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002213)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002213)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002213)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002213)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002213)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002213)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002213)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002213)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002213)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf100022200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002220) = true := by
  have h : ((childLL thetaAboveCell10002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002220) h
theorem e24KC2ThetaAboveLeaf100022201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002220) = true := by
  have h : ((childLH thetaAboveCell10002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002220) h
theorem e24KC2ThetaAboveLeaf100022202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002220) = true := by
  have h : ((childHL thetaAboveCell10002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002220) h
theorem e24KC2ThetaAboveLeaf100022203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002220) = true := by
  have h : ((childHH thetaAboveCell10002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002220) h
theorem e24KC2ThetaAboveLeaf100022210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002221) = true := by
  have h : ((childLL thetaAboveCell10002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002221) h
theorem e24KC2ThetaAboveLeaf100022211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002221) = true := by
  have h : ((childLH thetaAboveCell10002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002221) h
theorem e24KC2ThetaAboveLeaf100022212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002221) = true := by
  have h : ((childHL thetaAboveCell10002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002221) h
theorem e24KC2ThetaAboveLeaf100022213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002221) = true := by
  have h : ((childHH thetaAboveCell10002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002221) h
theorem e24KC2ThetaAboveLeaf10002222 :
    adaptiveCoverCheck 11 thetaAboveCell10002222 = true := by
  have h : (thetaAboveCell10002222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002222 h
theorem e24KC2ThetaAboveLeaf10002223 :
    adaptiveCoverCheck 11 thetaAboveCell10002223 = true := by
  have h : (thetaAboveCell10002223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002223 h
theorem e24KC2ThetaAboveLeaf100022300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002230) = true := by
  have h : ((childLL thetaAboveCell10002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002230) h
theorem e24KC2ThetaAboveLeaf100022301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002230) = true := by
  have h : ((childLH thetaAboveCell10002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002230) h
theorem e24KC2ThetaAboveLeaf100022302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002230) = true := by
  have h : ((childHL thetaAboveCell10002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002230) h
theorem e24KC2ThetaAboveLeaf100022303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002230) = true := by
  have h : ((childHH thetaAboveCell10002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002230) h
theorem e24KC2ThetaAboveLeaf100022310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002231) = true := by
  have h : ((childLL thetaAboveCell10002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002231) h
theorem e24KC2ThetaAboveLeaf100022311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002231) = true := by
  have h : ((childLH thetaAboveCell10002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002231) h
theorem e24KC2ThetaAboveLeaf100022312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002231) = true := by
  have h : ((childHL thetaAboveCell10002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002231) h
theorem e24KC2ThetaAboveLeaf100022313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002231) = true := by
  have h : ((childHH thetaAboveCell10002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002231) h
theorem e24KC2ThetaAboveLeaf10002232 :
    adaptiveCoverCheck 11 thetaAboveCell10002232 = true := by
  have h : (thetaAboveCell10002232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002232 h
theorem e24KC2ThetaAboveLeaf10002233 :
    adaptiveCoverCheck 11 thetaAboveCell10002233 = true := by
  have h : (thetaAboveCell10002233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002233 h
theorem e24KC2ThetaAboveLeaf100023000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002300) = true := by
  have h : ((childLL thetaAboveCell10002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002300) h
theorem e24KC2ThetaAboveLeaf100023001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002300) = true := by
  have h : ((childLH thetaAboveCell10002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002300) h
theorem e24KC2ThetaAboveLeaf100023002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002300) = true := by
  have h : ((childHL thetaAboveCell10002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002300) h
theorem e24KC2ThetaAboveLeaf100023003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002300) = true := by
  have h : ((childHH thetaAboveCell10002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002300) h
theorem e24KC2ThetaAboveLeaf100023010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002301) = true := by
  have h : ((childLL thetaAboveCell10002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002301) h
theorem e24KC2ThetaAboveLeaf100023011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002301) = true := by
  have h : ((childLH thetaAboveCell10002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002301) h
theorem e24KC2ThetaAboveLeaf100023012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002301) = true := by
  have h : ((childHL thetaAboveCell10002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002301) h
theorem e24KC2ThetaAboveLeaf100023013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002301) = true := by
  have h : ((childHH thetaAboveCell10002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002301) h
theorem e24KC2ThetaAboveLeaf1000230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002302)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002302)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002302)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002302)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002302)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002302)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002302)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002302)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002302)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002302)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002302)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002302)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002302)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002302)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002302)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002302)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002303)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002303)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002303)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002303)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002303)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002303)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002303)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002303)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002303)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002303)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002303)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002303)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002303)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002303)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002303)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002303)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf100023100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002310) = true := by
  have h : ((childLL thetaAboveCell10002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002310) h
theorem e24KC2ThetaAboveLeaf100023101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002310) = true := by
  have h : ((childLH thetaAboveCell10002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002310) h
theorem e24KC2ThetaAboveLeaf100023102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002310) = true := by
  have h : ((childHL thetaAboveCell10002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002310) h
theorem e24KC2ThetaAboveLeaf100023103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002310) = true := by
  have h : ((childHH thetaAboveCell10002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002310) h
theorem e24KC2ThetaAboveLeaf100023110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002311) = true := by
  have h : ((childLL thetaAboveCell10002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002311) h
theorem e24KC2ThetaAboveLeaf100023111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002311) = true := by
  have h : ((childLH thetaAboveCell10002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002311) h
theorem e24KC2ThetaAboveLeaf100023112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002311) = true := by
  have h : ((childHL thetaAboveCell10002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002311) h
theorem e24KC2ThetaAboveLeaf100023113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002311) = true := by
  have h : ((childHH thetaAboveCell10002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002311) h
theorem e24KC2ThetaAboveLeaf1000231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002312)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002312)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002312)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002312)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002312)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002312)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002312)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002312)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002312)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002312)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002312)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002312)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002312)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002312)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002312)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002312)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002313)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002313)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002313)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002313)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002313)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002313)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002313)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002313)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002313)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002313)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002313)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002313)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002313)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002313)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002313)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002313)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf100023200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002320) = true := by
  have h : ((childLL thetaAboveCell10002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002320) h
theorem e24KC2ThetaAboveLeaf100023201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002320) = true := by
  have h : ((childLH thetaAboveCell10002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002320) h
theorem e24KC2ThetaAboveLeaf100023202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002320) = true := by
  have h : ((childHL thetaAboveCell10002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002320) h
theorem e24KC2ThetaAboveLeaf100023203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002320) = true := by
  have h : ((childHH thetaAboveCell10002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002320) h
theorem e24KC2ThetaAboveLeaf100023210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002321) = true := by
  have h : ((childLL thetaAboveCell10002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002321) h
theorem e24KC2ThetaAboveLeaf100023211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002321) = true := by
  have h : ((childLH thetaAboveCell10002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002321) h
theorem e24KC2ThetaAboveLeaf100023212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002321) = true := by
  have h : ((childHL thetaAboveCell10002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002321) h
theorem e24KC2ThetaAboveLeaf100023213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002321) = true := by
  have h : ((childHH thetaAboveCell10002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002321) h
theorem e24KC2ThetaAboveLeaf10002322 :
    adaptiveCoverCheck 11 thetaAboveCell10002322 = true := by
  have h : (thetaAboveCell10002322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002322 h
theorem e24KC2ThetaAboveLeaf10002323 :
    adaptiveCoverCheck 11 thetaAboveCell10002323 = true := by
  have h : (thetaAboveCell10002323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002323 h
theorem e24KC2ThetaAboveLeaf100023300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002330) = true := by
  have h : ((childLL thetaAboveCell10002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002330) h
theorem e24KC2ThetaAboveLeaf100023301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002330) = true := by
  have h : ((childLH thetaAboveCell10002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002330) h
theorem e24KC2ThetaAboveLeaf100023302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002330) = true := by
  have h : ((childHL thetaAboveCell10002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002330) h
theorem e24KC2ThetaAboveLeaf100023303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002330) = true := by
  have h : ((childHH thetaAboveCell10002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002330) h
theorem e24KC2ThetaAboveLeaf100023310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002331) = true := by
  have h : ((childLL thetaAboveCell10002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002331) h
theorem e24KC2ThetaAboveLeaf100023311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002331) = true := by
  have h : ((childLH thetaAboveCell10002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002331) h
theorem e24KC2ThetaAboveLeaf100023312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002331) = true := by
  have h : ((childHL thetaAboveCell10002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002331) h
theorem e24KC2ThetaAboveLeaf100023313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002331) = true := by
  have h : ((childHH thetaAboveCell10002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002331) h
theorem e24KC2ThetaAboveLeaf10002332 :
    adaptiveCoverCheck 11 thetaAboveCell10002332 = true := by
  have h : (thetaAboveCell10002332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002332 h
theorem e24KC2ThetaAboveLeaf10002333 :
    adaptiveCoverCheck 11 thetaAboveCell10002333 = true := by
  have h : (thetaAboveCell10002333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002333 h
theorem e24KC2ThetaAboveLeaf1000300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1000))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf1000301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1000))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf10003020 :
    adaptiveCoverCheck 11 thetaAboveCell10003020 = true := by
  have h : (thetaAboveCell10003020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003020 h
theorem e24KC2ThetaAboveLeaf10003021 :
    adaptiveCoverCheck 11 thetaAboveCell10003021 = true := by
  have h : (thetaAboveCell10003021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003021 h
theorem e24KC2ThetaAboveLeaf10003022 :
    adaptiveCoverCheck 11 thetaAboveCell10003022 = true := by
  have h : (thetaAboveCell10003022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003022 h
theorem e24KC2ThetaAboveLeaf10003023 :
    adaptiveCoverCheck 11 thetaAboveCell10003023 = true := by
  have h : (thetaAboveCell10003023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003023 h
theorem e24KC2ThetaAboveLeaf10003030 :
    adaptiveCoverCheck 11 thetaAboveCell10003030 = true := by
  have h : (thetaAboveCell10003030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003030 h
theorem e24KC2ThetaAboveLeaf10003031 :
    adaptiveCoverCheck 11 thetaAboveCell10003031 = true := by
  have h : (thetaAboveCell10003031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003031 h
theorem e24KC2ThetaAboveLeaf10003032 :
    adaptiveCoverCheck 11 thetaAboveCell10003032 = true := by
  have h : (thetaAboveCell10003032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003032 h
theorem e24KC2ThetaAboveLeaf10003033 :
    adaptiveCoverCheck 11 thetaAboveCell10003033 = true := by
  have h : (thetaAboveCell10003033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003033 h
theorem e24KC2ThetaAboveLeaf1000310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1000))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf1000311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1000))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf10003120 :
    adaptiveCoverCheck 11 thetaAboveCell10003120 = true := by
  have h : (thetaAboveCell10003120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003120 h
theorem e24KC2ThetaAboveLeaf10003121 :
    adaptiveCoverCheck 11 thetaAboveCell10003121 = true := by
  have h : (thetaAboveCell10003121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003121 h
theorem e24KC2ThetaAboveLeaf10003122 :
    adaptiveCoverCheck 11 thetaAboveCell10003122 = true := by
  have h : (thetaAboveCell10003122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003122 h
theorem e24KC2ThetaAboveLeaf10003123 :
    adaptiveCoverCheck 11 thetaAboveCell10003123 = true := by
  have h : (thetaAboveCell10003123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003123 h
theorem e24KC2ThetaAboveLeaf10003130 :
    adaptiveCoverCheck 11 thetaAboveCell10003130 = true := by
  have h : (thetaAboveCell10003130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003130 h
theorem e24KC2ThetaAboveLeaf10003131 :
    adaptiveCoverCheck 11 thetaAboveCell10003131 = true := by
  have h : (thetaAboveCell10003131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003131 h
theorem e24KC2ThetaAboveLeaf10003132 :
    adaptiveCoverCheck 11 thetaAboveCell10003132 = true := by
  have h : (thetaAboveCell10003132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003132 h
theorem e24KC2ThetaAboveLeaf10003133 :
    adaptiveCoverCheck 11 thetaAboveCell10003133 = true := by
  have h : (thetaAboveCell10003133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003133 h
theorem e24KC2ThetaAboveLeaf100032000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003200) = true := by
  have h : ((childLL thetaAboveCell10003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003200) h
theorem e24KC2ThetaAboveLeaf100032001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003200) = true := by
  have h : ((childLH thetaAboveCell10003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003200) h
theorem e24KC2ThetaAboveLeaf100032002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003200) = true := by
  have h : ((childHL thetaAboveCell10003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003200) h
theorem e24KC2ThetaAboveLeaf100032003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003200) = true := by
  have h : ((childHH thetaAboveCell10003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003200) h
theorem e24KC2ThetaAboveLeaf100032010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003201) = true := by
  have h : ((childLL thetaAboveCell10003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003201) h
theorem e24KC2ThetaAboveLeaf100032011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003201) = true := by
  have h : ((childLH thetaAboveCell10003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003201) h
theorem e24KC2ThetaAboveLeaf100032012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003201) = true := by
  have h : ((childHL thetaAboveCell10003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003201) h
theorem e24KC2ThetaAboveLeaf100032013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003201) = true := by
  have h : ((childHH thetaAboveCell10003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003201) h
theorem e24KC2ThetaAboveLeaf1000320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003202)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003202)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003202)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003202)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003202)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003202)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003202)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003202)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003202)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003202)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003202)) h

end PartE
end GerverSofa

end

end

end
