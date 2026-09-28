/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT512000013`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells168aeb56e4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1011 : AngleCell :=
  childLH (childLH (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1012 : AngleCell :=
  childHL (childLH (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1013 : AngleCell :=
  childHH (childLH (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1020 : AngleCell :=
  childLL (childHL (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1021 : AngleCell :=
  childLH (childHL (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1022 : AngleCell :=
  childHL (childHL (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1023 : AngleCell :=
  childHH (childHL (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1030 : AngleCell :=
  childLL (childHH (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1031 : AngleCell :=
  childLH (childHH (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1032 : AngleCell :=
  childHL (childHH (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1033 : AngleCell :=
  childHH (childHH (childLL (childLH e24ThetaAboveRoot)))
/-- Subcell `1100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24ThetaAboveRoot)))
/-- Subcell `10103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10103333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1010)))
/-- Subcell `10112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1011)))
/-- Subcell `10112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10112333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1011)))
/-- Subcell `10113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1011)))
/-- Subcell `10113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1011)))
/-- Subcell `10113333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1011)))
/-- Subcell `11002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1100)))
/-- Subcell `11002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11002333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11002333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1100)))
/-- Subcell `11003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1100)))
/-- Subcell `11003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1100)))
/-- Subcell `11003330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11003330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1100)))

end CertificateCells168aeb56e4

open CertificateCells168aeb56e4
theorem e24KC2ThetaAboveLeaf101033002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103300) = true := by
  have h : ((childHL thetaAboveCell10103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103300) h
theorem e24KC2ThetaAboveLeaf101033003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103300) = true := by
  have h : ((childHH thetaAboveCell10103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103300) h
theorem e24KC2ThetaAboveLeaf101033010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103301) = true := by
  have h : ((childLL thetaAboveCell10103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103301) h
theorem e24KC2ThetaAboveLeaf101033011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103301) = true := by
  have h : ((childLH thetaAboveCell10103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103301) h
theorem e24KC2ThetaAboveLeaf101033012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103301) = true := by
  have h : ((childHL thetaAboveCell10103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103301) h
theorem e24KC2ThetaAboveLeaf101033013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103301) = true := by
  have h : ((childHH thetaAboveCell10103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103301) h
theorem e24KC2ThetaAboveLeaf1010330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10103302)) = true := by
  have h : ((childLL (childLL thetaAboveCell10103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10103302)) h
theorem e24KC2ThetaAboveLeaf1010330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10103302)) = true := by
  have h : ((childLH (childLL thetaAboveCell10103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10103302)) h
theorem e24KC2ThetaAboveLeaf1010330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10103302)) = true := by
  have h : ((childHL (childLL thetaAboveCell10103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10103302)) h
theorem e24KC2ThetaAboveLeaf1010330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10103302)) = true := by
  have h : ((childHH (childLL thetaAboveCell10103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10103302)) h
theorem e24KC2ThetaAboveLeaf101033021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103302) = true := by
  have h : ((childLH thetaAboveCell10103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103302) h
theorem e24KC2ThetaAboveLeaf101033022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103302) = true := by
  have h : ((childHL thetaAboveCell10103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103302) h
theorem e24KC2ThetaAboveLeaf101033023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103302) = true := by
  have h : ((childHH thetaAboveCell10103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103302) h
theorem e24KC2ThetaAboveLeaf101033030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103303) = true := by
  have h : ((childLL thetaAboveCell10103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103303) h
theorem e24KC2ThetaAboveLeaf101033031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103303) = true := by
  have h : ((childLH thetaAboveCell10103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103303) h
theorem e24KC2ThetaAboveLeaf101033032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103303) = true := by
  have h : ((childHL thetaAboveCell10103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103303) h
theorem e24KC2ThetaAboveLeaf101033033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103303) = true := by
  have h : ((childHH thetaAboveCell10103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103303) h
theorem e24KC2ThetaAboveLeaf101033100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103310) = true := by
  have h : ((childLL thetaAboveCell10103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103310) h
theorem e24KC2ThetaAboveLeaf101033101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103310) = true := by
  have h : ((childLH thetaAboveCell10103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103310) h
theorem e24KC2ThetaAboveLeaf101033102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103310) = true := by
  have h : ((childHL thetaAboveCell10103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103310) h
theorem e24KC2ThetaAboveLeaf101033103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103310) = true := by
  have h : ((childHH thetaAboveCell10103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103310) h
theorem e24KC2ThetaAboveLeaf101033110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103311) = true := by
  have h : ((childLL thetaAboveCell10103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103311) h
theorem e24KC2ThetaAboveLeaf101033111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103311) = true := by
  have h : ((childLH thetaAboveCell10103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103311) h
theorem e24KC2ThetaAboveLeaf101033112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103311) = true := by
  have h : ((childHL thetaAboveCell10103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103311) h
theorem e24KC2ThetaAboveLeaf101033113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103311) = true := by
  have h : ((childHH thetaAboveCell10103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103311) h
theorem e24KC2ThetaAboveLeaf101033120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103312) = true := by
  have h : ((childLL thetaAboveCell10103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103312) h
theorem e24KC2ThetaAboveLeaf101033121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103312) = true := by
  have h : ((childLH thetaAboveCell10103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103312) h
theorem e24KC2ThetaAboveLeaf101033122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103312) = true := by
  have h : ((childHL thetaAboveCell10103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103312) h
theorem e24KC2ThetaAboveLeaf101033123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103312) = true := by
  have h : ((childHH thetaAboveCell10103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103312) h
theorem e24KC2ThetaAboveLeaf101033130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103313) = true := by
  have h : ((childLL thetaAboveCell10103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103313) h
theorem e24KC2ThetaAboveLeaf101033131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103313) = true := by
  have h : ((childLH thetaAboveCell10103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103313) h
theorem e24KC2ThetaAboveLeaf101033132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103313) = true := by
  have h : ((childHL thetaAboveCell10103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103313) h
theorem e24KC2ThetaAboveLeaf101033133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103313) = true := by
  have h : ((childHH thetaAboveCell10103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103313) h
theorem e24KC2ThetaAboveLeaf101033200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103320) = true := by
  have h : ((childLL thetaAboveCell10103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103320) h
theorem e24KC2ThetaAboveLeaf101033201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103320) = true := by
  have h : ((childLH thetaAboveCell10103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103320) h
theorem e24KC2ThetaAboveLeaf101033202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103320) = true := by
  have h : ((childHL thetaAboveCell10103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103320) h
theorem e24KC2ThetaAboveLeaf101033203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103320) = true := by
  have h : ((childHH thetaAboveCell10103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103320) h
theorem e24KC2ThetaAboveLeaf101033210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103321) = true := by
  have h : ((childLL thetaAboveCell10103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103321) h
theorem e24KC2ThetaAboveLeaf101033211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103321) = true := by
  have h : ((childLH thetaAboveCell10103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103321) h
theorem e24KC2ThetaAboveLeaf101033212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103321) = true := by
  have h : ((childHL thetaAboveCell10103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103321) h
theorem e24KC2ThetaAboveLeaf101033213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103321) = true := by
  have h : ((childHH thetaAboveCell10103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103321) h
theorem e24KC2ThetaAboveLeaf10103322 :
    adaptiveCoverCheck 11 thetaAboveCell10103322 = true := by
  have h : (thetaAboveCell10103322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10103322 h
theorem e24KC2ThetaAboveLeaf10103323 :
    adaptiveCoverCheck 11 thetaAboveCell10103323 = true := by
  have h : (thetaAboveCell10103323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10103323 h
theorem e24KC2ThetaAboveLeaf101033300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103330) = true := by
  have h : ((childLL thetaAboveCell10103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103330) h
theorem e24KC2ThetaAboveLeaf101033301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103330) = true := by
  have h : ((childLH thetaAboveCell10103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103330) h
theorem e24KC2ThetaAboveLeaf101033302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103330) = true := by
  have h : ((childHL thetaAboveCell10103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103330) h
theorem e24KC2ThetaAboveLeaf101033303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103330) = true := by
  have h : ((childHH thetaAboveCell10103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103330) h
theorem e24KC2ThetaAboveLeaf101033310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103331) = true := by
  have h : ((childLL thetaAboveCell10103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103331) h
theorem e24KC2ThetaAboveLeaf101033311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103331) = true := by
  have h : ((childLH thetaAboveCell10103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103331) h
theorem e24KC2ThetaAboveLeaf101033312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103331) = true := by
  have h : ((childHL thetaAboveCell10103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103331) h
theorem e24KC2ThetaAboveLeaf101033313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103331) = true := by
  have h : ((childHH thetaAboveCell10103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103331) h
theorem e24KC2ThetaAboveLeaf10103332 :
    adaptiveCoverCheck 11 thetaAboveCell10103332 = true := by
  have h : (thetaAboveCell10103332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10103332 h
theorem e24KC2ThetaAboveLeaf10103333 :
    adaptiveCoverCheck 11 thetaAboveCell10103333 = true := by
  have h : (thetaAboveCell10103333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10103333 h
theorem e24KC2ThetaAboveLeaf101100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1011)) = true := by
  have h : ((childLL (childLL thetaAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1011)) h
theorem e24KC2ThetaAboveLeaf101101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1011)) = true := by
  have h : ((childLH (childLL thetaAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1011)) h
theorem e24KC2ThetaAboveLeaf101102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1011)) = true := by
  have h : ((childHL (childLL thetaAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1011)) h
theorem e24KC2ThetaAboveLeaf101103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1011)) = true := by
  have h : ((childHH (childLL thetaAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1011)) h
theorem e24KC2ThetaAboveLeaf101110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1011)) = true := by
  have h : ((childLL (childLH thetaAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1011)) h
theorem e24KC2ThetaAboveLeaf101111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1011)) = true := by
  have h : ((childLH (childLH thetaAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1011)) h
theorem e24KC2ThetaAboveLeaf101112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1011)) = true := by
  have h : ((childHL (childLH thetaAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1011)) h
theorem e24KC2ThetaAboveLeaf101113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1011)) = true := by
  have h : ((childHH (childLH thetaAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1011)) h
theorem e24KC2ThetaAboveLeaf1011200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1011))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1011))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell1011))) = true := by
  have h : ((childHL (childLL (childHL thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell1011))) = true := by
  have h : ((childHH (childLL (childHL thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1011))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1011))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell1011))) = true := by
  have h : ((childHL (childLH (childHL thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell1011))) = true := by
  have h : ((childHH (childLH (childHL thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf101122000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112200) = true := by
  have h : ((childLL thetaAboveCell10112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112200) h
theorem e24KC2ThetaAboveLeaf101122001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112200) = true := by
  have h : ((childLH thetaAboveCell10112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112200) h
theorem e24KC2ThetaAboveLeaf101122002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112200) = true := by
  have h : ((childHL thetaAboveCell10112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112200) h
theorem e24KC2ThetaAboveLeaf101122003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112200) = true := by
  have h : ((childHH thetaAboveCell10112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112200) h
theorem e24KC2ThetaAboveLeaf101122010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112201) = true := by
  have h : ((childLL thetaAboveCell10112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112201) h
theorem e24KC2ThetaAboveLeaf101122011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112201) = true := by
  have h : ((childLH thetaAboveCell10112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112201) h
theorem e24KC2ThetaAboveLeaf101122012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112201) = true := by
  have h : ((childHL thetaAboveCell10112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112201) h
theorem e24KC2ThetaAboveLeaf101122013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112201) = true := by
  have h : ((childHH thetaAboveCell10112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112201) h
theorem e24KC2ThetaAboveLeaf101122020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112202) = true := by
  have h : ((childLL thetaAboveCell10112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112202) h
theorem e24KC2ThetaAboveLeaf101122021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112202) = true := by
  have h : ((childLH thetaAboveCell10112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112202) h
theorem e24KC2ThetaAboveLeaf101122022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112202) = true := by
  have h : ((childHL thetaAboveCell10112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112202) h
theorem e24KC2ThetaAboveLeaf101122023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112202) = true := by
  have h : ((childHH thetaAboveCell10112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112202) h
theorem e24KC2ThetaAboveLeaf101122030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112203) = true := by
  have h : ((childLL thetaAboveCell10112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112203) h
theorem e24KC2ThetaAboveLeaf101122031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112203) = true := by
  have h : ((childLH thetaAboveCell10112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112203) h
theorem e24KC2ThetaAboveLeaf101122032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112203) = true := by
  have h : ((childHL thetaAboveCell10112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112203) h
theorem e24KC2ThetaAboveLeaf101122033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112203) = true := by
  have h : ((childHH thetaAboveCell10112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112203) h
theorem e24KC2ThetaAboveLeaf101122100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112210) = true := by
  have h : ((childLL thetaAboveCell10112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112210) h
theorem e24KC2ThetaAboveLeaf101122101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112210) = true := by
  have h : ((childLH thetaAboveCell10112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112210) h
theorem e24KC2ThetaAboveLeaf101122102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112210) = true := by
  have h : ((childHL thetaAboveCell10112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112210) h
theorem e24KC2ThetaAboveLeaf101122103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112210) = true := by
  have h : ((childHH thetaAboveCell10112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112210) h
theorem e24KC2ThetaAboveLeaf101122110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112211) = true := by
  have h : ((childLL thetaAboveCell10112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112211) h
theorem e24KC2ThetaAboveLeaf101122111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112211) = true := by
  have h : ((childLH thetaAboveCell10112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112211) h
theorem e24KC2ThetaAboveLeaf101122112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112211) = true := by
  have h : ((childHL thetaAboveCell10112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112211) h
theorem e24KC2ThetaAboveLeaf101122113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112211) = true := by
  have h : ((childHH thetaAboveCell10112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112211) h
theorem e24KC2ThetaAboveLeaf101122120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112212) = true := by
  have h : ((childLL thetaAboveCell10112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112212) h
theorem e24KC2ThetaAboveLeaf101122121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112212) = true := by
  have h : ((childLH thetaAboveCell10112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112212) h
theorem e24KC2ThetaAboveLeaf101122122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112212) = true := by
  have h : ((childHL thetaAboveCell10112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112212) h
theorem e24KC2ThetaAboveLeaf101122123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112212) = true := by
  have h : ((childHH thetaAboveCell10112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112212) h
theorem e24KC2ThetaAboveLeaf101122130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112213) = true := by
  have h : ((childLL thetaAboveCell10112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112213) h
theorem e24KC2ThetaAboveLeaf101122131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112213) = true := by
  have h : ((childLH thetaAboveCell10112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112213) h
theorem e24KC2ThetaAboveLeaf101122132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112213) = true := by
  have h : ((childHL thetaAboveCell10112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112213) h
theorem e24KC2ThetaAboveLeaf101122133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112213) = true := by
  have h : ((childHH thetaAboveCell10112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112213) h
theorem e24KC2ThetaAboveLeaf101122200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112220) = true := by
  have h : ((childLL thetaAboveCell10112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112220) h
theorem e24KC2ThetaAboveLeaf101122201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112220) = true := by
  have h : ((childLH thetaAboveCell10112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112220) h
theorem e24KC2ThetaAboveLeaf101122202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112220) = true := by
  have h : ((childHL thetaAboveCell10112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112220) h
theorem e24KC2ThetaAboveLeaf101122203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112220) = true := by
  have h : ((childHH thetaAboveCell10112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112220) h
theorem e24KC2ThetaAboveLeaf101122210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112221) = true := by
  have h : ((childLL thetaAboveCell10112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112221) h
theorem e24KC2ThetaAboveLeaf101122211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112221) = true := by
  have h : ((childLH thetaAboveCell10112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112221) h
theorem e24KC2ThetaAboveLeaf101122212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112221) = true := by
  have h : ((childHL thetaAboveCell10112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112221) h
theorem e24KC2ThetaAboveLeaf101122213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112221) = true := by
  have h : ((childHH thetaAboveCell10112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112221) h
theorem e24KC2ThetaAboveLeaf10112222 :
    adaptiveCoverCheck 11 thetaAboveCell10112222 = true := by
  have h : (thetaAboveCell10112222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10112222 h
theorem e24KC2ThetaAboveLeaf10112223 :
    adaptiveCoverCheck 11 thetaAboveCell10112223 = true := by
  have h : (thetaAboveCell10112223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10112223 h
theorem e24KC2ThetaAboveLeaf101122300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112230) = true := by
  have h : ((childLL thetaAboveCell10112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112230) h
theorem e24KC2ThetaAboveLeaf101122301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112230) = true := by
  have h : ((childLH thetaAboveCell10112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112230) h
theorem e24KC2ThetaAboveLeaf101122302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112230) = true := by
  have h : ((childHL thetaAboveCell10112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112230) h
theorem e24KC2ThetaAboveLeaf101122303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112230) = true := by
  have h : ((childHH thetaAboveCell10112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112230) h
theorem e24KC2ThetaAboveLeaf101122310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112231) = true := by
  have h : ((childLL thetaAboveCell10112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112231) h
theorem e24KC2ThetaAboveLeaf101122311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112231) = true := by
  have h : ((childLH thetaAboveCell10112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112231) h
theorem e24KC2ThetaAboveLeaf101122312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112231) = true := by
  have h : ((childHL thetaAboveCell10112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112231) h
theorem e24KC2ThetaAboveLeaf101122313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112231) = true := by
  have h : ((childHH thetaAboveCell10112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112231) h
theorem e24KC2ThetaAboveLeaf10112232 :
    adaptiveCoverCheck 11 thetaAboveCell10112232 = true := by
  have h : (thetaAboveCell10112232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10112232 h
theorem e24KC2ThetaAboveLeaf10112233 :
    adaptiveCoverCheck 11 thetaAboveCell10112233 = true := by
  have h : (thetaAboveCell10112233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10112233 h
theorem e24KC2ThetaAboveLeaf101123000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112300) = true := by
  have h : ((childLL thetaAboveCell10112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112300) h
theorem e24KC2ThetaAboveLeaf101123001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112300) = true := by
  have h : ((childLH thetaAboveCell10112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112300) h
theorem e24KC2ThetaAboveLeaf101123002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112300) = true := by
  have h : ((childHL thetaAboveCell10112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112300) h
theorem e24KC2ThetaAboveLeaf101123003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112300) = true := by
  have h : ((childHH thetaAboveCell10112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112300) h
theorem e24KC2ThetaAboveLeaf101123010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112301) = true := by
  have h : ((childLL thetaAboveCell10112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112301) h
theorem e24KC2ThetaAboveLeaf101123011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112301) = true := by
  have h : ((childLH thetaAboveCell10112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112301) h
theorem e24KC2ThetaAboveLeaf101123012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112301) = true := by
  have h : ((childHL thetaAboveCell10112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112301) h
theorem e24KC2ThetaAboveLeaf101123013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112301) = true := by
  have h : ((childHH thetaAboveCell10112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112301) h
theorem e24KC2ThetaAboveLeaf101123020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112302) = true := by
  have h : ((childLL thetaAboveCell10112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112302) h
theorem e24KC2ThetaAboveLeaf101123021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112302) = true := by
  have h : ((childLH thetaAboveCell10112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112302) h
theorem e24KC2ThetaAboveLeaf101123022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112302) = true := by
  have h : ((childHL thetaAboveCell10112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112302) h
theorem e24KC2ThetaAboveLeaf101123023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112302) = true := by
  have h : ((childHH thetaAboveCell10112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112302) h
theorem e24KC2ThetaAboveLeaf101123030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112303) = true := by
  have h : ((childLL thetaAboveCell10112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112303) h
theorem e24KC2ThetaAboveLeaf101123031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112303) = true := by
  have h : ((childLH thetaAboveCell10112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112303) h
theorem e24KC2ThetaAboveLeaf101123032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112303) = true := by
  have h : ((childHL thetaAboveCell10112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112303) h
theorem e24KC2ThetaAboveLeaf101123033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112303) = true := by
  have h : ((childHH thetaAboveCell10112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112303) h
theorem e24KC2ThetaAboveLeaf101123100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112310) = true := by
  have h : ((childLL thetaAboveCell10112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112310) h
theorem e24KC2ThetaAboveLeaf101123101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112310) = true := by
  have h : ((childLH thetaAboveCell10112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112310) h
theorem e24KC2ThetaAboveLeaf101123102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112310) = true := by
  have h : ((childHL thetaAboveCell10112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112310) h
theorem e24KC2ThetaAboveLeaf101123103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112310) = true := by
  have h : ((childHH thetaAboveCell10112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112310) h
theorem e24KC2ThetaAboveLeaf101123110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112311) = true := by
  have h : ((childLL thetaAboveCell10112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112311) h
theorem e24KC2ThetaAboveLeaf101123111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112311) = true := by
  have h : ((childLH thetaAboveCell10112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112311) h
theorem e24KC2ThetaAboveLeaf101123112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112311) = true := by
  have h : ((childHL thetaAboveCell10112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112311) h
theorem e24KC2ThetaAboveLeaf101123113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112311) = true := by
  have h : ((childHH thetaAboveCell10112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112311) h
theorem e24KC2ThetaAboveLeaf101123120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112312) = true := by
  have h : ((childLL thetaAboveCell10112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112312) h
theorem e24KC2ThetaAboveLeaf101123121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112312) = true := by
  have h : ((childLH thetaAboveCell10112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112312) h
theorem e24KC2ThetaAboveLeaf101123122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112312) = true := by
  have h : ((childHL thetaAboveCell10112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112312) h
theorem e24KC2ThetaAboveLeaf101123123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112312) = true := by
  have h : ((childHH thetaAboveCell10112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112312) h
theorem e24KC2ThetaAboveLeaf101123130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112313) = true := by
  have h : ((childLL thetaAboveCell10112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112313) h
theorem e24KC2ThetaAboveLeaf101123131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112313) = true := by
  have h : ((childLH thetaAboveCell10112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112313) h
theorem e24KC2ThetaAboveLeaf101123132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112313) = true := by
  have h : ((childHL thetaAboveCell10112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112313) h
theorem e24KC2ThetaAboveLeaf101123133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112313) = true := by
  have h : ((childHH thetaAboveCell10112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112313) h
theorem e24KC2ThetaAboveLeaf101123200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112320) = true := by
  have h : ((childLL thetaAboveCell10112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112320) h
theorem e24KC2ThetaAboveLeaf101123201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112320) = true := by
  have h : ((childLH thetaAboveCell10112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112320) h
theorem e24KC2ThetaAboveLeaf101123202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112320) = true := by
  have h : ((childHL thetaAboveCell10112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112320) h
theorem e24KC2ThetaAboveLeaf101123203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112320) = true := by
  have h : ((childHH thetaAboveCell10112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112320) h
theorem e24KC2ThetaAboveLeaf101123210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112321) = true := by
  have h : ((childLL thetaAboveCell10112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112321) h
theorem e24KC2ThetaAboveLeaf101123211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112321) = true := by
  have h : ((childLH thetaAboveCell10112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112321) h
theorem e24KC2ThetaAboveLeaf101123212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112321) = true := by
  have h : ((childHL thetaAboveCell10112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112321) h
theorem e24KC2ThetaAboveLeaf101123213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112321) = true := by
  have h : ((childHH thetaAboveCell10112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112321) h
theorem e24KC2ThetaAboveLeaf10112322 :
    adaptiveCoverCheck 11 thetaAboveCell10112322 = true := by
  have h : (thetaAboveCell10112322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10112322 h
theorem e24KC2ThetaAboveLeaf10112323 :
    adaptiveCoverCheck 11 thetaAboveCell10112323 = true := by
  have h : (thetaAboveCell10112323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10112323 h
theorem e24KC2ThetaAboveLeaf101123300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112330) = true := by
  have h : ((childLL thetaAboveCell10112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112330) h
theorem e24KC2ThetaAboveLeaf101123301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112330) = true := by
  have h : ((childLH thetaAboveCell10112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112330) h
theorem e24KC2ThetaAboveLeaf101123302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112330) = true := by
  have h : ((childHL thetaAboveCell10112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112330) h
theorem e24KC2ThetaAboveLeaf101123303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112330) = true := by
  have h : ((childHH thetaAboveCell10112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112330) h
theorem e24KC2ThetaAboveLeaf101123310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10112331) = true := by
  have h : ((childLL thetaAboveCell10112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10112331) h
theorem e24KC2ThetaAboveLeaf101123311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10112331) = true := by
  have h : ((childLH thetaAboveCell10112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10112331) h
theorem e24KC2ThetaAboveLeaf101123312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10112331) = true := by
  have h : ((childHL thetaAboveCell10112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10112331) h
theorem e24KC2ThetaAboveLeaf101123313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10112331) = true := by
  have h : ((childHH thetaAboveCell10112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10112331) h
theorem e24KC2ThetaAboveLeaf10112332 :
    adaptiveCoverCheck 11 thetaAboveCell10112332 = true := by
  have h : (thetaAboveCell10112332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10112332 h
theorem e24KC2ThetaAboveLeaf10112333 :
    adaptiveCoverCheck 11 thetaAboveCell10112333 = true := by
  have h : (thetaAboveCell10112333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10112333 h
theorem e24KC2ThetaAboveLeaf1011300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1011))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1011))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1011))) = true := by
  have h : ((childHL (childLL (childHH thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1011))) = true := by
  have h : ((childHH (childLL (childHH thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1011))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1011))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1011))) = true := by
  have h : ((childHL (childLH (childHH thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf1011313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1011))) = true := by
  have h : ((childHH (childLH (childHH thetaAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH thetaAboveCell1011))) h
theorem e24KC2ThetaAboveLeaf101132000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113200) = true := by
  have h : ((childLL thetaAboveCell10113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113200) h
theorem e24KC2ThetaAboveLeaf101132001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113200) = true := by
  have h : ((childLH thetaAboveCell10113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113200) h
theorem e24KC2ThetaAboveLeaf101132002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113200) = true := by
  have h : ((childHL thetaAboveCell10113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113200) h
theorem e24KC2ThetaAboveLeaf101132003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113200) = true := by
  have h : ((childHH thetaAboveCell10113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113200) h
theorem e24KC2ThetaAboveLeaf101132010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113201) = true := by
  have h : ((childLL thetaAboveCell10113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113201) h
theorem e24KC2ThetaAboveLeaf101132011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113201) = true := by
  have h : ((childLH thetaAboveCell10113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113201) h
theorem e24KC2ThetaAboveLeaf101132012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113201) = true := by
  have h : ((childHL thetaAboveCell10113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113201) h
theorem e24KC2ThetaAboveLeaf101132013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113201) = true := by
  have h : ((childHH thetaAboveCell10113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113201) h
theorem e24KC2ThetaAboveLeaf101132020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113202) = true := by
  have h : ((childLL thetaAboveCell10113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113202) h
theorem e24KC2ThetaAboveLeaf101132021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113202) = true := by
  have h : ((childLH thetaAboveCell10113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113202) h
theorem e24KC2ThetaAboveLeaf101132022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113202) = true := by
  have h : ((childHL thetaAboveCell10113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113202) h
theorem e24KC2ThetaAboveLeaf101132023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113202) = true := by
  have h : ((childHH thetaAboveCell10113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113202) h
theorem e24KC2ThetaAboveLeaf101132030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113203) = true := by
  have h : ((childLL thetaAboveCell10113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113203) h
theorem e24KC2ThetaAboveLeaf101132031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113203) = true := by
  have h : ((childLH thetaAboveCell10113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113203) h
theorem e24KC2ThetaAboveLeaf101132032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113203) = true := by
  have h : ((childHL thetaAboveCell10113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113203) h
theorem e24KC2ThetaAboveLeaf101132033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113203) = true := by
  have h : ((childHH thetaAboveCell10113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113203) h
theorem e24KC2ThetaAboveLeaf101132100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113210) = true := by
  have h : ((childLL thetaAboveCell10113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113210) h
theorem e24KC2ThetaAboveLeaf101132101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113210) = true := by
  have h : ((childLH thetaAboveCell10113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113210) h
theorem e24KC2ThetaAboveLeaf101132102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113210) = true := by
  have h : ((childHL thetaAboveCell10113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113210) h
theorem e24KC2ThetaAboveLeaf101132103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113210) = true := by
  have h : ((childHH thetaAboveCell10113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113210) h
theorem e24KC2ThetaAboveLeaf101132110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113211) = true := by
  have h : ((childLL thetaAboveCell10113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113211) h
theorem e24KC2ThetaAboveLeaf101132111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113211) = true := by
  have h : ((childLH thetaAboveCell10113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113211) h
theorem e24KC2ThetaAboveLeaf101132112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113211) = true := by
  have h : ((childHL thetaAboveCell10113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113211) h
theorem e24KC2ThetaAboveLeaf101132113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113211) = true := by
  have h : ((childHH thetaAboveCell10113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113211) h
theorem e24KC2ThetaAboveLeaf101132120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113212) = true := by
  have h : ((childLL thetaAboveCell10113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113212) h
theorem e24KC2ThetaAboveLeaf101132121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113212) = true := by
  have h : ((childLH thetaAboveCell10113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113212) h
theorem e24KC2ThetaAboveLeaf101132122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113212) = true := by
  have h : ((childHL thetaAboveCell10113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113212) h
theorem e24KC2ThetaAboveLeaf101132123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113212) = true := by
  have h : ((childHH thetaAboveCell10113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113212) h
theorem e24KC2ThetaAboveLeaf101132130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113213) = true := by
  have h : ((childLL thetaAboveCell10113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113213) h
theorem e24KC2ThetaAboveLeaf101132131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113213) = true := by
  have h : ((childLH thetaAboveCell10113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113213) h
theorem e24KC2ThetaAboveLeaf101132132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113213) = true := by
  have h : ((childHL thetaAboveCell10113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113213) h
theorem e24KC2ThetaAboveLeaf101132133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113213) = true := by
  have h : ((childHH thetaAboveCell10113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113213) h
theorem e24KC2ThetaAboveLeaf101132200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113220) = true := by
  have h : ((childLL thetaAboveCell10113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113220) h
theorem e24KC2ThetaAboveLeaf101132201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113220) = true := by
  have h : ((childLH thetaAboveCell10113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113220) h
theorem e24KC2ThetaAboveLeaf101132202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113220) = true := by
  have h : ((childHL thetaAboveCell10113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113220) h
theorem e24KC2ThetaAboveLeaf101132203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113220) = true := by
  have h : ((childHH thetaAboveCell10113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113220) h
theorem e24KC2ThetaAboveLeaf101132210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113221) = true := by
  have h : ((childLL thetaAboveCell10113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113221) h
theorem e24KC2ThetaAboveLeaf101132211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113221) = true := by
  have h : ((childLH thetaAboveCell10113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113221) h
theorem e24KC2ThetaAboveLeaf101132212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113221) = true := by
  have h : ((childHL thetaAboveCell10113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113221) h
theorem e24KC2ThetaAboveLeaf101132213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113221) = true := by
  have h : ((childHH thetaAboveCell10113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113221) h
theorem e24KC2ThetaAboveLeaf10113222 :
    adaptiveCoverCheck 11 thetaAboveCell10113222 = true := by
  have h : (thetaAboveCell10113222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10113222 h
theorem e24KC2ThetaAboveLeaf10113223 :
    adaptiveCoverCheck 11 thetaAboveCell10113223 = true := by
  have h : (thetaAboveCell10113223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10113223 h
theorem e24KC2ThetaAboveLeaf101132300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113230) = true := by
  have h : ((childLL thetaAboveCell10113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113230) h
theorem e24KC2ThetaAboveLeaf101132301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113230) = true := by
  have h : ((childLH thetaAboveCell10113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113230) h
theorem e24KC2ThetaAboveLeaf101132302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113230) = true := by
  have h : ((childHL thetaAboveCell10113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113230) h
theorem e24KC2ThetaAboveLeaf101132303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113230) = true := by
  have h : ((childHH thetaAboveCell10113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113230) h
theorem e24KC2ThetaAboveLeaf101132310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113231) = true := by
  have h : ((childLL thetaAboveCell10113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113231) h
theorem e24KC2ThetaAboveLeaf101132311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113231) = true := by
  have h : ((childLH thetaAboveCell10113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113231) h
theorem e24KC2ThetaAboveLeaf101132312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113231) = true := by
  have h : ((childHL thetaAboveCell10113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113231) h
theorem e24KC2ThetaAboveLeaf101132313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113231) = true := by
  have h : ((childHH thetaAboveCell10113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113231) h
theorem e24KC2ThetaAboveLeaf10113232 :
    adaptiveCoverCheck 11 thetaAboveCell10113232 = true := by
  have h : (thetaAboveCell10113232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10113232 h
theorem e24KC2ThetaAboveLeaf10113233 :
    adaptiveCoverCheck 11 thetaAboveCell10113233 = true := by
  have h : (thetaAboveCell10113233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10113233 h
theorem e24KC2ThetaAboveLeaf101133000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113300) = true := by
  have h : ((childLL thetaAboveCell10113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113300) h
theorem e24KC2ThetaAboveLeaf101133001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113300) = true := by
  have h : ((childLH thetaAboveCell10113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113300) h
theorem e24KC2ThetaAboveLeaf101133002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113300) = true := by
  have h : ((childHL thetaAboveCell10113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113300) h
theorem e24KC2ThetaAboveLeaf101133003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113300) = true := by
  have h : ((childHH thetaAboveCell10113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113300) h
theorem e24KC2ThetaAboveLeaf101133010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113301) = true := by
  have h : ((childLL thetaAboveCell10113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113301) h
theorem e24KC2ThetaAboveLeaf101133011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113301) = true := by
  have h : ((childLH thetaAboveCell10113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113301) h
theorem e24KC2ThetaAboveLeaf101133012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113301) = true := by
  have h : ((childHL thetaAboveCell10113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113301) h
theorem e24KC2ThetaAboveLeaf101133013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113301) = true := by
  have h : ((childHH thetaAboveCell10113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113301) h
theorem e24KC2ThetaAboveLeaf101133020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113302) = true := by
  have h : ((childLL thetaAboveCell10113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113302) h
theorem e24KC2ThetaAboveLeaf101133021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113302) = true := by
  have h : ((childLH thetaAboveCell10113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113302) h
theorem e24KC2ThetaAboveLeaf101133022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113302) = true := by
  have h : ((childHL thetaAboveCell10113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113302) h
theorem e24KC2ThetaAboveLeaf101133023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113302) = true := by
  have h : ((childHH thetaAboveCell10113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113302) h
theorem e24KC2ThetaAboveLeaf101133030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113303) = true := by
  have h : ((childLL thetaAboveCell10113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113303) h
theorem e24KC2ThetaAboveLeaf101133031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113303) = true := by
  have h : ((childLH thetaAboveCell10113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113303) h
theorem e24KC2ThetaAboveLeaf101133032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113303) = true := by
  have h : ((childHL thetaAboveCell10113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113303) h
theorem e24KC2ThetaAboveLeaf101133033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113303) = true := by
  have h : ((childHH thetaAboveCell10113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113303) h
theorem e24KC2ThetaAboveLeaf101133100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113310) = true := by
  have h : ((childLL thetaAboveCell10113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113310) h
theorem e24KC2ThetaAboveLeaf101133101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113310) = true := by
  have h : ((childLH thetaAboveCell10113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113310) h
theorem e24KC2ThetaAboveLeaf101133102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113310) = true := by
  have h : ((childHL thetaAboveCell10113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113310) h
theorem e24KC2ThetaAboveLeaf101133103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113310) = true := by
  have h : ((childHH thetaAboveCell10113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113310) h
theorem e24KC2ThetaAboveLeaf101133110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113311) = true := by
  have h : ((childLL thetaAboveCell10113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113311) h
theorem e24KC2ThetaAboveLeaf101133111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113311) = true := by
  have h : ((childLH thetaAboveCell10113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113311) h
theorem e24KC2ThetaAboveLeaf101133112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113311) = true := by
  have h : ((childHL thetaAboveCell10113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113311) h
theorem e24KC2ThetaAboveLeaf101133113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113311) = true := by
  have h : ((childHH thetaAboveCell10113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113311) h
theorem e24KC2ThetaAboveLeaf101133120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113312) = true := by
  have h : ((childLL thetaAboveCell10113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113312) h
theorem e24KC2ThetaAboveLeaf101133121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113312) = true := by
  have h : ((childLH thetaAboveCell10113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113312) h
theorem e24KC2ThetaAboveLeaf101133122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113312) = true := by
  have h : ((childHL thetaAboveCell10113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113312) h
theorem e24KC2ThetaAboveLeaf101133123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113312) = true := by
  have h : ((childHH thetaAboveCell10113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113312) h
theorem e24KC2ThetaAboveLeaf101133130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113313) = true := by
  have h : ((childLL thetaAboveCell10113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113313) h
theorem e24KC2ThetaAboveLeaf101133131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113313) = true := by
  have h : ((childLH thetaAboveCell10113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113313) h
theorem e24KC2ThetaAboveLeaf101133132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113313) = true := by
  have h : ((childHL thetaAboveCell10113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113313) h
theorem e24KC2ThetaAboveLeaf101133133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113313) = true := by
  have h : ((childHH thetaAboveCell10113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113313) h
theorem e24KC2ThetaAboveLeaf101133200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113320) = true := by
  have h : ((childLL thetaAboveCell10113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113320) h
theorem e24KC2ThetaAboveLeaf101133201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113320) = true := by
  have h : ((childLH thetaAboveCell10113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113320) h
theorem e24KC2ThetaAboveLeaf101133202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113320) = true := by
  have h : ((childHL thetaAboveCell10113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113320) h
theorem e24KC2ThetaAboveLeaf101133203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113320) = true := by
  have h : ((childHH thetaAboveCell10113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113320) h
theorem e24KC2ThetaAboveLeaf101133210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113321) = true := by
  have h : ((childLL thetaAboveCell10113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113321) h
theorem e24KC2ThetaAboveLeaf101133211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113321) = true := by
  have h : ((childLH thetaAboveCell10113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113321) h
theorem e24KC2ThetaAboveLeaf101133212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113321) = true := by
  have h : ((childHL thetaAboveCell10113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113321) h
theorem e24KC2ThetaAboveLeaf101133213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113321) = true := by
  have h : ((childHH thetaAboveCell10113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113321) h
theorem e24KC2ThetaAboveLeaf10113322 :
    adaptiveCoverCheck 11 thetaAboveCell10113322 = true := by
  have h : (thetaAboveCell10113322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10113322 h
theorem e24KC2ThetaAboveLeaf10113323 :
    adaptiveCoverCheck 11 thetaAboveCell10113323 = true := by
  have h : (thetaAboveCell10113323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10113323 h
theorem e24KC2ThetaAboveLeaf101133300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113330) = true := by
  have h : ((childLL thetaAboveCell10113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113330) h
theorem e24KC2ThetaAboveLeaf101133301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113330) = true := by
  have h : ((childLH thetaAboveCell10113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113330) h
theorem e24KC2ThetaAboveLeaf101133302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113330) = true := by
  have h : ((childHL thetaAboveCell10113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113330) h
theorem e24KC2ThetaAboveLeaf101133303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113330) = true := by
  have h : ((childHH thetaAboveCell10113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113330) h
theorem e24KC2ThetaAboveLeaf101133310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10113331) = true := by
  have h : ((childLL thetaAboveCell10113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10113331) h
theorem e24KC2ThetaAboveLeaf101133311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10113331) = true := by
  have h : ((childLH thetaAboveCell10113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10113331) h
theorem e24KC2ThetaAboveLeaf101133312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10113331) = true := by
  have h : ((childHL thetaAboveCell10113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10113331) h
theorem e24KC2ThetaAboveLeaf101133313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10113331) = true := by
  have h : ((childHH thetaAboveCell10113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10113331) h
theorem e24KC2ThetaAboveLeaf10113332 :
    adaptiveCoverCheck 11 thetaAboveCell10113332 = true := by
  have h : (thetaAboveCell10113332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10113332 h
theorem e24KC2ThetaAboveLeaf10113333 :
    adaptiveCoverCheck 11 thetaAboveCell10113333 = true := by
  have h : (thetaAboveCell10113333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10113333 h
theorem e24KC2ThetaAboveLeaf1012000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1012))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1012))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1012))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1012))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1012))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1012))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1012))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1012))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf101202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1012)) = true := by
  have h : ((childHL (childLL thetaAboveCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1012)) h
theorem e24KC2ThetaAboveLeaf101203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1012)) = true := by
  have h : ((childHH (childLL thetaAboveCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1012)) h
theorem e24KC2ThetaAboveLeaf1012100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1012))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1012))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1012))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1012))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1012))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1012))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1012))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf1012113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1012))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1012)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1012))) h
theorem e24KC2ThetaAboveLeaf101212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1012)) = true := by
  have h : ((childHL (childLH thetaAboveCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1012)) h
theorem e24KC2ThetaAboveLeaf101213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1012)) = true := by
  have h : ((childHH (childLH thetaAboveCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1012)) h
theorem e24KC2ThetaAboveLeaf10122 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1012) = true := by
  have h : ((childHL thetaAboveCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1012) h
theorem e24KC2ThetaAboveLeaf10123 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1012) = true := by
  have h : ((childHH thetaAboveCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1012) h
theorem e24KC2ThetaAboveLeaf1013000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1013))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1013))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1013))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1013))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1013))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1013))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1013))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1013))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf101302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1013)) = true := by
  have h : ((childHL (childLL thetaAboveCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1013)) h
theorem e24KC2ThetaAboveLeaf101303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1013)) = true := by
  have h : ((childHH (childLL thetaAboveCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1013)) h
theorem e24KC2ThetaAboveLeaf1013100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1013))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1013))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1013))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1013))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1013))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1013))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1013))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf1013113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1013))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1013)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1013))) h
theorem e24KC2ThetaAboveLeaf101312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1013)) = true := by
  have h : ((childHL (childLH thetaAboveCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1013)) h
theorem e24KC2ThetaAboveLeaf101313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1013)) = true := by
  have h : ((childHH (childLH thetaAboveCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1013)) h
theorem e24KC2ThetaAboveLeaf10132 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1013) = true := by
  have h : ((childHL thetaAboveCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1013) h
theorem e24KC2ThetaAboveLeaf10133 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1013) = true := by
  have h : ((childHH thetaAboveCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1013) h
theorem e24KC2ThetaAboveLeaf1020 :
    adaptiveCoverCheck 15 thetaAboveCell1020 = true := by
  have h : (thetaAboveCell1020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1020 h
theorem e24KC2ThetaAboveLeaf1021 :
    adaptiveCoverCheck 15 thetaAboveCell1021 = true := by
  have h : (thetaAboveCell1021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1021 h
theorem e24KC2ThetaAboveLeaf1022 :
    adaptiveCoverCheck 15 thetaAboveCell1022 = true := by
  have h : (thetaAboveCell1022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1022 h
theorem e24KC2ThetaAboveLeaf1023 :
    adaptiveCoverCheck 15 thetaAboveCell1023 = true := by
  have h : (thetaAboveCell1023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1023 h
theorem e24KC2ThetaAboveLeaf1030 :
    adaptiveCoverCheck 15 thetaAboveCell1030 = true := by
  have h : (thetaAboveCell1030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1030 h
theorem e24KC2ThetaAboveLeaf1031 :
    adaptiveCoverCheck 15 thetaAboveCell1031 = true := by
  have h : (thetaAboveCell1031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1031 h
theorem e24KC2ThetaAboveLeaf1032 :
    adaptiveCoverCheck 15 thetaAboveCell1032 = true := by
  have h : (thetaAboveCell1032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1032 h
theorem e24KC2ThetaAboveLeaf1033 :
    adaptiveCoverCheck 15 thetaAboveCell1033 = true := by
  have h : (thetaAboveCell1033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1033 h
theorem e24KC2ThetaAboveLeaf110000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1100)) = true := by
  have h : ((childLL (childLL thetaAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1100)) h
theorem e24KC2ThetaAboveLeaf110001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1100)) = true := by
  have h : ((childLH (childLL thetaAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1100)) h
theorem e24KC2ThetaAboveLeaf110002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1100)) = true := by
  have h : ((childHL (childLL thetaAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1100)) h
theorem e24KC2ThetaAboveLeaf110003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1100)) = true := by
  have h : ((childHH (childLL thetaAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1100)) h
theorem e24KC2ThetaAboveLeaf110010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1100)) = true := by
  have h : ((childLL (childLH thetaAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1100)) h
theorem e24KC2ThetaAboveLeaf110011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1100)) = true := by
  have h : ((childLH (childLH thetaAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1100)) h
theorem e24KC2ThetaAboveLeaf110012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1100)) = true := by
  have h : ((childHL (childLH thetaAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1100)) h
theorem e24KC2ThetaAboveLeaf110013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1100)) = true := by
  have h : ((childHH (childLH thetaAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1100)) h
theorem e24KC2ThetaAboveLeaf1100200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1100))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1100))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell1100))) = true := by
  have h : ((childHL (childLL (childHL thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell1100))) = true := by
  have h : ((childHH (childLL (childHL thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1100))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1100))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell1100))) = true := by
  have h : ((childHL (childLH (childHL thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell1100))) = true := by
  have h : ((childHH (childLH (childHL thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf11002200 :
    adaptiveCoverCheck 11 thetaAboveCell11002200 = true := by
  have h : (thetaAboveCell11002200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002200 h
theorem e24KC2ThetaAboveLeaf11002201 :
    adaptiveCoverCheck 11 thetaAboveCell11002201 = true := by
  have h : (thetaAboveCell11002201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002201 h
theorem e24KC2ThetaAboveLeaf110022020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002202) = true := by
  have h : ((childLL thetaAboveCell11002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002202) h
theorem e24KC2ThetaAboveLeaf110022021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002202) = true := by
  have h : ((childLH thetaAboveCell11002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002202) h
theorem e24KC2ThetaAboveLeaf110022022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002202) = true := by
  have h : ((childHL thetaAboveCell11002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002202) h
theorem e24KC2ThetaAboveLeaf110022023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002202) = true := by
  have h : ((childHH thetaAboveCell11002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002202) h
theorem e24KC2ThetaAboveLeaf110022030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002203) = true := by
  have h : ((childLL thetaAboveCell11002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002203) h
theorem e24KC2ThetaAboveLeaf110022031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002203) = true := by
  have h : ((childLH thetaAboveCell11002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002203) h
theorem e24KC2ThetaAboveLeaf110022032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002203) = true := by
  have h : ((childHL thetaAboveCell11002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002203) h
theorem e24KC2ThetaAboveLeaf110022033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002203) = true := by
  have h : ((childHH thetaAboveCell11002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002203) h
theorem e24KC2ThetaAboveLeaf11002210 :
    adaptiveCoverCheck 11 thetaAboveCell11002210 = true := by
  have h : (thetaAboveCell11002210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002210 h
theorem e24KC2ThetaAboveLeaf11002211 :
    adaptiveCoverCheck 11 thetaAboveCell11002211 = true := by
  have h : (thetaAboveCell11002211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002211 h
theorem e24KC2ThetaAboveLeaf110022120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002212) = true := by
  have h : ((childLL thetaAboveCell11002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002212) h
theorem e24KC2ThetaAboveLeaf110022121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002212) = true := by
  have h : ((childLH thetaAboveCell11002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002212) h
theorem e24KC2ThetaAboveLeaf110022122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002212) = true := by
  have h : ((childHL thetaAboveCell11002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002212) h
theorem e24KC2ThetaAboveLeaf110022123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002212) = true := by
  have h : ((childHH thetaAboveCell11002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002212) h
theorem e24KC2ThetaAboveLeaf110022130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002213) = true := by
  have h : ((childLL thetaAboveCell11002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002213) h
theorem e24KC2ThetaAboveLeaf110022131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002213) = true := by
  have h : ((childLH thetaAboveCell11002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002213) h
theorem e24KC2ThetaAboveLeaf110022132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002213) = true := by
  have h : ((childHL thetaAboveCell11002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002213) h
theorem e24KC2ThetaAboveLeaf110022133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002213) = true := by
  have h : ((childHH thetaAboveCell11002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002213) h
theorem e24KC2ThetaAboveLeaf110022200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002220) = true := by
  have h : ((childLL thetaAboveCell11002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002220) h
theorem e24KC2ThetaAboveLeaf110022201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002220) = true := by
  have h : ((childLH thetaAboveCell11002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002220) h
theorem e24KC2ThetaAboveLeaf110022202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002220) = true := by
  have h : ((childHL thetaAboveCell11002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002220) h
theorem e24KC2ThetaAboveLeaf110022203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002220) = true := by
  have h : ((childHH thetaAboveCell11002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002220) h
theorem e24KC2ThetaAboveLeaf110022210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002221) = true := by
  have h : ((childLL thetaAboveCell11002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002221) h
theorem e24KC2ThetaAboveLeaf110022211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002221) = true := by
  have h : ((childLH thetaAboveCell11002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002221) h
theorem e24KC2ThetaAboveLeaf110022212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002221) = true := by
  have h : ((childHL thetaAboveCell11002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002221) h
theorem e24KC2ThetaAboveLeaf110022213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002221) = true := by
  have h : ((childHH thetaAboveCell11002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002221) h
theorem e24KC2ThetaAboveLeaf11002222 :
    adaptiveCoverCheck 11 thetaAboveCell11002222 = true := by
  have h : (thetaAboveCell11002222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002222 h
theorem e24KC2ThetaAboveLeaf11002223 :
    adaptiveCoverCheck 11 thetaAboveCell11002223 = true := by
  have h : (thetaAboveCell11002223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002223 h
theorem e24KC2ThetaAboveLeaf110022300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002230) = true := by
  have h : ((childLL thetaAboveCell11002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002230) h
theorem e24KC2ThetaAboveLeaf110022301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002230) = true := by
  have h : ((childLH thetaAboveCell11002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002230) h
theorem e24KC2ThetaAboveLeaf110022302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002230) = true := by
  have h : ((childHL thetaAboveCell11002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002230) h
theorem e24KC2ThetaAboveLeaf110022303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002230) = true := by
  have h : ((childHH thetaAboveCell11002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002230) h
theorem e24KC2ThetaAboveLeaf110022310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002231) = true := by
  have h : ((childLL thetaAboveCell11002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002231) h
theorem e24KC2ThetaAboveLeaf110022311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002231) = true := by
  have h : ((childLH thetaAboveCell11002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002231) h
theorem e24KC2ThetaAboveLeaf110022312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002231) = true := by
  have h : ((childHL thetaAboveCell11002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002231) h
theorem e24KC2ThetaAboveLeaf110022313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002231) = true := by
  have h : ((childHH thetaAboveCell11002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002231) h
theorem e24KC2ThetaAboveLeaf11002232 :
    adaptiveCoverCheck 11 thetaAboveCell11002232 = true := by
  have h : (thetaAboveCell11002232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002232 h
theorem e24KC2ThetaAboveLeaf11002233 :
    adaptiveCoverCheck 11 thetaAboveCell11002233 = true := by
  have h : (thetaAboveCell11002233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002233 h
theorem e24KC2ThetaAboveLeaf11002300 :
    adaptiveCoverCheck 11 thetaAboveCell11002300 = true := by
  have h : (thetaAboveCell11002300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002300 h
theorem e24KC2ThetaAboveLeaf11002301 :
    adaptiveCoverCheck 11 thetaAboveCell11002301 = true := by
  have h : (thetaAboveCell11002301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002301 h
theorem e24KC2ThetaAboveLeaf110023020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002302) = true := by
  have h : ((childLL thetaAboveCell11002302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002302) h
theorem e24KC2ThetaAboveLeaf110023021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002302) = true := by
  have h : ((childLH thetaAboveCell11002302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002302) h
theorem e24KC2ThetaAboveLeaf110023022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002302) = true := by
  have h : ((childHL thetaAboveCell11002302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002302) h
theorem e24KC2ThetaAboveLeaf110023023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002302) = true := by
  have h : ((childHH thetaAboveCell11002302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002302) h
theorem e24KC2ThetaAboveLeaf110023030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002303) = true := by
  have h : ((childLL thetaAboveCell11002303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002303) h
theorem e24KC2ThetaAboveLeaf110023031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002303) = true := by
  have h : ((childLH thetaAboveCell11002303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002303) h
theorem e24KC2ThetaAboveLeaf110023032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002303) = true := by
  have h : ((childHL thetaAboveCell11002303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002303) h
theorem e24KC2ThetaAboveLeaf110023033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002303) = true := by
  have h : ((childHH thetaAboveCell11002303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002303) h
theorem e24KC2ThetaAboveLeaf11002310 :
    adaptiveCoverCheck 11 thetaAboveCell11002310 = true := by
  have h : (thetaAboveCell11002310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002310 h
theorem e24KC2ThetaAboveLeaf11002311 :
    adaptiveCoverCheck 11 thetaAboveCell11002311 = true := by
  have h : (thetaAboveCell11002311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002311 h
theorem e24KC2ThetaAboveLeaf110023120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002312) = true := by
  have h : ((childLL thetaAboveCell11002312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002312) h
theorem e24KC2ThetaAboveLeaf110023121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002312) = true := by
  have h : ((childLH thetaAboveCell11002312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002312) h
theorem e24KC2ThetaAboveLeaf110023122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002312) = true := by
  have h : ((childHL thetaAboveCell11002312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002312) h
theorem e24KC2ThetaAboveLeaf110023123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002312) = true := by
  have h : ((childHH thetaAboveCell11002312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002312) h
theorem e24KC2ThetaAboveLeaf110023130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002313) = true := by
  have h : ((childLL thetaAboveCell11002313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002313) h
theorem e24KC2ThetaAboveLeaf110023131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002313) = true := by
  have h : ((childLH thetaAboveCell11002313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002313) h
theorem e24KC2ThetaAboveLeaf110023132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002313) = true := by
  have h : ((childHL thetaAboveCell11002313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002313) h
theorem e24KC2ThetaAboveLeaf110023133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002313) = true := by
  have h : ((childHH thetaAboveCell11002313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002313) h
theorem e24KC2ThetaAboveLeaf110023200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002320) = true := by
  have h : ((childLL thetaAboveCell11002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002320) h
theorem e24KC2ThetaAboveLeaf110023201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002320) = true := by
  have h : ((childLH thetaAboveCell11002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002320) h
theorem e24KC2ThetaAboveLeaf110023202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002320) = true := by
  have h : ((childHL thetaAboveCell11002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002320) h
theorem e24KC2ThetaAboveLeaf110023203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002320) = true := by
  have h : ((childHH thetaAboveCell11002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002320) h
theorem e24KC2ThetaAboveLeaf110023210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002321) = true := by
  have h : ((childLL thetaAboveCell11002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002321) h
theorem e24KC2ThetaAboveLeaf110023211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002321) = true := by
  have h : ((childLH thetaAboveCell11002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002321) h
theorem e24KC2ThetaAboveLeaf110023212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002321) = true := by
  have h : ((childHL thetaAboveCell11002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002321) h
theorem e24KC2ThetaAboveLeaf110023213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002321) = true := by
  have h : ((childHH thetaAboveCell11002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002321) h
theorem e24KC2ThetaAboveLeaf11002322 :
    adaptiveCoverCheck 11 thetaAboveCell11002322 = true := by
  have h : (thetaAboveCell11002322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002322 h
theorem e24KC2ThetaAboveLeaf11002323 :
    adaptiveCoverCheck 11 thetaAboveCell11002323 = true := by
  have h : (thetaAboveCell11002323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002323 h
theorem e24KC2ThetaAboveLeaf110023300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002330) = true := by
  have h : ((childLL thetaAboveCell11002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002330) h
theorem e24KC2ThetaAboveLeaf110023301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002330) = true := by
  have h : ((childLH thetaAboveCell11002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002330) h
theorem e24KC2ThetaAboveLeaf110023302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002330) = true := by
  have h : ((childHL thetaAboveCell11002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002330) h
theorem e24KC2ThetaAboveLeaf110023303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002330) = true := by
  have h : ((childHH thetaAboveCell11002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002330) h
theorem e24KC2ThetaAboveLeaf110023310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11002331) = true := by
  have h : ((childLL thetaAboveCell11002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11002331) h
theorem e24KC2ThetaAboveLeaf110023311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11002331) = true := by
  have h : ((childLH thetaAboveCell11002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11002331) h
theorem e24KC2ThetaAboveLeaf110023312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11002331) = true := by
  have h : ((childHL thetaAboveCell11002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11002331) h
theorem e24KC2ThetaAboveLeaf110023313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11002331) = true := by
  have h : ((childHH thetaAboveCell11002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11002331) h
theorem e24KC2ThetaAboveLeaf11002332 :
    adaptiveCoverCheck 11 thetaAboveCell11002332 = true := by
  have h : (thetaAboveCell11002332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002332 h
theorem e24KC2ThetaAboveLeaf11002333 :
    adaptiveCoverCheck 11 thetaAboveCell11002333 = true := by
  have h : (thetaAboveCell11002333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11002333 h
theorem e24KC2ThetaAboveLeaf1100300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1100))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1100))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1100))) = true := by
  have h : ((childHL (childLL (childHH thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1100))) = true := by
  have h : ((childHH (childLL (childHH thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1100))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1100))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1100))) = true := by
  have h : ((childHL (childLH (childHH thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf1100313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1100))) = true := by
  have h : ((childHH (childLH (childHH thetaAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH thetaAboveCell1100))) h
theorem e24KC2ThetaAboveLeaf11003200 :
    adaptiveCoverCheck 11 thetaAboveCell11003200 = true := by
  have h : (thetaAboveCell11003200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003200 h
theorem e24KC2ThetaAboveLeaf11003201 :
    adaptiveCoverCheck 11 thetaAboveCell11003201 = true := by
  have h : (thetaAboveCell11003201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003201 h
theorem e24KC2ThetaAboveLeaf110032020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003202) = true := by
  have h : ((childLL thetaAboveCell11003202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003202) h
theorem e24KC2ThetaAboveLeaf110032021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003202) = true := by
  have h : ((childLH thetaAboveCell11003202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003202) h
theorem e24KC2ThetaAboveLeaf110032022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003202) = true := by
  have h : ((childHL thetaAboveCell11003202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003202) h
theorem e24KC2ThetaAboveLeaf110032023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003202) = true := by
  have h : ((childHH thetaAboveCell11003202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003202) h
theorem e24KC2ThetaAboveLeaf110032030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003203) = true := by
  have h : ((childLL thetaAboveCell11003203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003203) h
theorem e24KC2ThetaAboveLeaf110032031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003203) = true := by
  have h : ((childLH thetaAboveCell11003203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003203) h
theorem e24KC2ThetaAboveLeaf110032032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003203) = true := by
  have h : ((childHL thetaAboveCell11003203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003203) h
theorem e24KC2ThetaAboveLeaf110032033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003203) = true := by
  have h : ((childHH thetaAboveCell11003203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003203) h
theorem e24KC2ThetaAboveLeaf11003210 :
    adaptiveCoverCheck 11 thetaAboveCell11003210 = true := by
  have h : (thetaAboveCell11003210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003210 h
theorem e24KC2ThetaAboveLeaf11003211 :
    adaptiveCoverCheck 11 thetaAboveCell11003211 = true := by
  have h : (thetaAboveCell11003211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003211 h
theorem e24KC2ThetaAboveLeaf110032120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003212) = true := by
  have h : ((childLL thetaAboveCell11003212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003212) h
theorem e24KC2ThetaAboveLeaf110032121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003212) = true := by
  have h : ((childLH thetaAboveCell11003212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003212) h
theorem e24KC2ThetaAboveLeaf110032122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003212) = true := by
  have h : ((childHL thetaAboveCell11003212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003212) h
theorem e24KC2ThetaAboveLeaf110032123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003212) = true := by
  have h : ((childHH thetaAboveCell11003212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003212) h
theorem e24KC2ThetaAboveLeaf110032130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003213) = true := by
  have h : ((childLL thetaAboveCell11003213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003213) h
theorem e24KC2ThetaAboveLeaf110032131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003213) = true := by
  have h : ((childLH thetaAboveCell11003213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003213) h
theorem e24KC2ThetaAboveLeaf110032132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003213) = true := by
  have h : ((childHL thetaAboveCell11003213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003213) h
theorem e24KC2ThetaAboveLeaf110032133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003213) = true := by
  have h : ((childHH thetaAboveCell11003213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003213) h
theorem e24KC2ThetaAboveLeaf110032200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003220) = true := by
  have h : ((childLL thetaAboveCell11003220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003220) h
theorem e24KC2ThetaAboveLeaf110032201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003220) = true := by
  have h : ((childLH thetaAboveCell11003220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003220) h
theorem e24KC2ThetaAboveLeaf110032202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003220) = true := by
  have h : ((childHL thetaAboveCell11003220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003220) h
theorem e24KC2ThetaAboveLeaf110032203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003220) = true := by
  have h : ((childHH thetaAboveCell11003220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003220) h
theorem e24KC2ThetaAboveLeaf110032210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003221) = true := by
  have h : ((childLL thetaAboveCell11003221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003221) h
theorem e24KC2ThetaAboveLeaf110032211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003221) = true := by
  have h : ((childLH thetaAboveCell11003221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003221) h
theorem e24KC2ThetaAboveLeaf110032212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003221) = true := by
  have h : ((childHL thetaAboveCell11003221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003221) h
theorem e24KC2ThetaAboveLeaf110032213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003221) = true := by
  have h : ((childHH thetaAboveCell11003221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003221) h
theorem e24KC2ThetaAboveLeaf11003222 :
    adaptiveCoverCheck 11 thetaAboveCell11003222 = true := by
  have h : (thetaAboveCell11003222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003222 h
theorem e24KC2ThetaAboveLeaf11003223 :
    adaptiveCoverCheck 11 thetaAboveCell11003223 = true := by
  have h : (thetaAboveCell11003223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003223 h
theorem e24KC2ThetaAboveLeaf110032300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003230) = true := by
  have h : ((childLL thetaAboveCell11003230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003230) h
theorem e24KC2ThetaAboveLeaf110032301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003230) = true := by
  have h : ((childLH thetaAboveCell11003230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003230) h
theorem e24KC2ThetaAboveLeaf110032302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003230) = true := by
  have h : ((childHL thetaAboveCell11003230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003230) h
theorem e24KC2ThetaAboveLeaf110032303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003230) = true := by
  have h : ((childHH thetaAboveCell11003230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003230) h
theorem e24KC2ThetaAboveLeaf110032310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003231) = true := by
  have h : ((childLL thetaAboveCell11003231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003231) h
theorem e24KC2ThetaAboveLeaf110032311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003231) = true := by
  have h : ((childLH thetaAboveCell11003231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003231) h
theorem e24KC2ThetaAboveLeaf110032312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003231) = true := by
  have h : ((childHL thetaAboveCell11003231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003231) h
theorem e24KC2ThetaAboveLeaf110032313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003231) = true := by
  have h : ((childHH thetaAboveCell11003231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003231) h
theorem e24KC2ThetaAboveLeaf11003232 :
    adaptiveCoverCheck 11 thetaAboveCell11003232 = true := by
  have h : (thetaAboveCell11003232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003232 h
theorem e24KC2ThetaAboveLeaf11003233 :
    adaptiveCoverCheck 11 thetaAboveCell11003233 = true := by
  have h : (thetaAboveCell11003233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003233 h
theorem e24KC2ThetaAboveLeaf11003300 :
    adaptiveCoverCheck 11 thetaAboveCell11003300 = true := by
  have h : (thetaAboveCell11003300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003300 h
theorem e24KC2ThetaAboveLeaf11003301 :
    adaptiveCoverCheck 11 thetaAboveCell11003301 = true := by
  have h : (thetaAboveCell11003301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003301 h
theorem e24KC2ThetaAboveLeaf110033020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003302) = true := by
  have h : ((childLL thetaAboveCell11003302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003302) h
theorem e24KC2ThetaAboveLeaf110033021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003302) = true := by
  have h : ((childLH thetaAboveCell11003302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003302) h
theorem e24KC2ThetaAboveLeaf110033022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003302) = true := by
  have h : ((childHL thetaAboveCell11003302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003302) h
theorem e24KC2ThetaAboveLeaf110033023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003302) = true := by
  have h : ((childHH thetaAboveCell11003302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003302) h
theorem e24KC2ThetaAboveLeaf110033030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003303) = true := by
  have h : ((childLL thetaAboveCell11003303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003303) h
theorem e24KC2ThetaAboveLeaf110033031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003303) = true := by
  have h : ((childLH thetaAboveCell11003303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003303) h
theorem e24KC2ThetaAboveLeaf110033032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003303) = true := by
  have h : ((childHL thetaAboveCell11003303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003303) h
theorem e24KC2ThetaAboveLeaf110033033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003303) = true := by
  have h : ((childHH thetaAboveCell11003303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003303) h
theorem e24KC2ThetaAboveLeaf11003310 :
    adaptiveCoverCheck 11 thetaAboveCell11003310 = true := by
  have h : (thetaAboveCell11003310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003310 h
theorem e24KC2ThetaAboveLeaf11003311 :
    adaptiveCoverCheck 11 thetaAboveCell11003311 = true := by
  have h : (thetaAboveCell11003311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003311 h
theorem e24KC2ThetaAboveLeaf110033120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003312) = true := by
  have h : ((childLL thetaAboveCell11003312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003312) h
theorem e24KC2ThetaAboveLeaf110033121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003312) = true := by
  have h : ((childLH thetaAboveCell11003312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003312) h
theorem e24KC2ThetaAboveLeaf110033122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003312) = true := by
  have h : ((childHL thetaAboveCell11003312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003312) h
theorem e24KC2ThetaAboveLeaf110033123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003312) = true := by
  have h : ((childHH thetaAboveCell11003312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003312) h
theorem e24KC2ThetaAboveLeaf110033130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003313) = true := by
  have h : ((childLL thetaAboveCell11003313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003313) h
theorem e24KC2ThetaAboveLeaf110033131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003313) = true := by
  have h : ((childLH thetaAboveCell11003313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003313) h
theorem e24KC2ThetaAboveLeaf110033132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003313) = true := by
  have h : ((childHL thetaAboveCell11003313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003313) h
theorem e24KC2ThetaAboveLeaf110033133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003313) = true := by
  have h : ((childHH thetaAboveCell11003313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003313) h
theorem e24KC2ThetaAboveLeaf110033200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003320) = true := by
  have h : ((childLL thetaAboveCell11003320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003320) h
theorem e24KC2ThetaAboveLeaf110033201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003320) = true := by
  have h : ((childLH thetaAboveCell11003320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003320) h
theorem e24KC2ThetaAboveLeaf110033202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003320) = true := by
  have h : ((childHL thetaAboveCell11003320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003320) h
theorem e24KC2ThetaAboveLeaf110033203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003320) = true := by
  have h : ((childHH thetaAboveCell11003320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003320) h
theorem e24KC2ThetaAboveLeaf110033210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003321) = true := by
  have h : ((childLL thetaAboveCell11003321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003321) h
theorem e24KC2ThetaAboveLeaf110033211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11003321) = true := by
  have h : ((childLH thetaAboveCell11003321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11003321) h
theorem e24KC2ThetaAboveLeaf110033212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11003321) = true := by
  have h : ((childHL thetaAboveCell11003321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11003321) h
theorem e24KC2ThetaAboveLeaf110033213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11003321) = true := by
  have h : ((childHH thetaAboveCell11003321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11003321) h
theorem e24KC2ThetaAboveLeaf11003322 :
    adaptiveCoverCheck 11 thetaAboveCell11003322 = true := by
  have h : (thetaAboveCell11003322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003322 h
theorem e24KC2ThetaAboveLeaf11003323 :
    adaptiveCoverCheck 11 thetaAboveCell11003323 = true := by
  have h : (thetaAboveCell11003323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11003323 h
theorem e24KC2ThetaAboveLeaf110033300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11003330) = true := by
  have h : ((childLL thetaAboveCell11003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11003330) h

end PartE
end GerverSofa

end

end

end
