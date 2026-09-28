/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT102400005`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3b1d8a0c5a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0002 : AngleCell :=
  childHL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0003 : AngleCell :=
  childHH (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `0011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00013333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0001)))
/-- Subcell `00102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0010)))
/-- Subcell `00102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0010)))
/-- Subcell `00102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0010)))
/-- Subcell `00102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0010)))
/-- Subcell `00102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0010)))
/-- Subcell `00102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0010)))
/-- Subcell `00102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0010)))
/-- Subcell `00102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0010)))
/-- Subcell `00102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0010)))
/-- Subcell `00102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0010)))
/-- Subcell `00102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0010)))
/-- Subcell `00102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0010)))
/-- Subcell `00102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0010)))
/-- Subcell `00102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0010)))
/-- Subcell `00102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0010)))
/-- Subcell `00102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0010)))
/-- Subcell `00102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0010)))
/-- Subcell `00102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00102333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0010)))
/-- Subcell `00103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0010)))
/-- Subcell `00103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0010)))
/-- Subcell `00103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0010)))
/-- Subcell `00103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0010)))
/-- Subcell `00103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0010)))
/-- Subcell `00103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0010)))
/-- Subcell `00103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0010)))
/-- Subcell `00103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0010)))
/-- Subcell `00103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0010)))
/-- Subcell `00103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0010)))
/-- Subcell `00103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0010)))
/-- Subcell `00103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0010)))
/-- Subcell `00103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0010)))
/-- Subcell `00103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0010)))
/-- Subcell `00103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0010)))
/-- Subcell `00103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0010)))
/-- Subcell `00103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0010)))
/-- Subcell `00103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00103333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0010)))
/-- Subcell `00112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0011)))
/-- Subcell `00112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0011)))
/-- Subcell `00112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0011)))
/-- Subcell `00112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0011)))
/-- Subcell `00112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0011)))
/-- Subcell `00112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0011)))
/-- Subcell `00112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0011)))
/-- Subcell `00112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0011)))
/-- Subcell `00112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0011)))
/-- Subcell `00112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0011)))
/-- Subcell `00112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0011)))
/-- Subcell `00112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0011)))
/-- Subcell `00112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0011)))
/-- Subcell `00112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0011)))
/-- Subcell `00112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0011)))
/-- Subcell `00112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0011)))
/-- Subcell `00112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0011)))
/-- Subcell `00112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0011)))
/-- Subcell `00112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0011)))

end CertificateCells3b1d8a0c5a

open CertificateCells3b1d8a0c5a
theorem e24KC2ThetaAboveLeaf0001331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013312)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013312)) h
theorem e24KC2ThetaAboveLeaf0001331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013312)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013312)) h
theorem e24KC2ThetaAboveLeaf0001331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013312)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013312)) h
theorem e24KC2ThetaAboveLeaf0001331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013312)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013312)) h
theorem e24KC2ThetaAboveLeaf0001331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013312)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013312)) h
theorem e24KC2ThetaAboveLeaf0001331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013312)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013312)) h
theorem e24KC2ThetaAboveLeaf000133122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013312) = true := by
  have h : ((childHL thetaAboveCell00013312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013312) h
theorem e24KC2ThetaAboveLeaf000133123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013312) = true := by
  have h : ((childHH thetaAboveCell00013312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013312) h
theorem e24KC2ThetaAboveLeaf0001331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013313)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013313)) h
theorem e24KC2ThetaAboveLeaf0001331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013313)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013313)) h
theorem e24KC2ThetaAboveLeaf0001331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013313)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013313)) h
theorem e24KC2ThetaAboveLeaf0001331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013313)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013313)) h
theorem e24KC2ThetaAboveLeaf0001331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013313)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013313)) h
theorem e24KC2ThetaAboveLeaf000133132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013313) = true := by
  have h : ((childHL thetaAboveCell00013313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013313) h
theorem e24KC2ThetaAboveLeaf000133133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013313) = true := by
  have h : ((childHH thetaAboveCell00013313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013313) h
theorem e24KC2ThetaAboveLeaf00013320 :
    adaptiveCoverCheck 11 thetaAboveCell00013320 = true := by
  have h : (thetaAboveCell00013320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013320 h
theorem e24KC2ThetaAboveLeaf00013321 :
    adaptiveCoverCheck 11 thetaAboveCell00013321 = true := by
  have h : (thetaAboveCell00013321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013321 h
theorem e24KC2ThetaAboveLeaf00013322 :
    adaptiveCoverCheck 11 thetaAboveCell00013322 = true := by
  have h : (thetaAboveCell00013322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013322 h
theorem e24KC2ThetaAboveLeaf00013323 :
    adaptiveCoverCheck 11 thetaAboveCell00013323 = true := by
  have h : (thetaAboveCell00013323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013323 h
theorem e24KC2ThetaAboveLeaf00013330 :
    adaptiveCoverCheck 11 thetaAboveCell00013330 = true := by
  have h : (thetaAboveCell00013330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013330 h
theorem e24KC2ThetaAboveLeaf00013331 :
    adaptiveCoverCheck 11 thetaAboveCell00013331 = true := by
  have h : (thetaAboveCell00013331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013331 h
theorem e24KC2ThetaAboveLeaf00013332 :
    adaptiveCoverCheck 11 thetaAboveCell00013332 = true := by
  have h : (thetaAboveCell00013332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013332 h
theorem e24KC2ThetaAboveLeaf00013333 :
    adaptiveCoverCheck 11 thetaAboveCell00013333 = true := by
  have h : (thetaAboveCell00013333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013333 h
theorem e24KC2ThetaAboveLeaf0002000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0002))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0002))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0002))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0002))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0002))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0002))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0002))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0002))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf000202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0002)) = true := by
  have h : ((childHL (childLL thetaAboveCell0002))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0002)) h
theorem e24KC2ThetaAboveLeaf000203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0002)) = true := by
  have h : ((childHH (childLL thetaAboveCell0002))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0002)) h
theorem e24KC2ThetaAboveLeaf0002100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0002))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0002))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0002))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0002))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0002))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0002))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0002))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf0002113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0002))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0002))) h
theorem e24KC2ThetaAboveLeaf000212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0002)) = true := by
  have h : ((childHL (childLH thetaAboveCell0002))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0002)) h
theorem e24KC2ThetaAboveLeaf000213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0002)) = true := by
  have h : ((childHH (childLH thetaAboveCell0002))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0002)) h
theorem e24KC2ThetaAboveLeaf00022 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0002) = true := by
  have h : ((childHL thetaAboveCell0002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0002) h
theorem e24KC2ThetaAboveLeaf00023 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0002) = true := by
  have h : ((childHH thetaAboveCell0002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0002) h
theorem e24KC2ThetaAboveLeaf0003000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0003))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0003))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0003))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0003))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0003))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0003))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0003))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0003))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf000302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0003)) = true := by
  have h : ((childHL (childLL thetaAboveCell0003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0003)) h
theorem e24KC2ThetaAboveLeaf000303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0003)) = true := by
  have h : ((childHH (childLL thetaAboveCell0003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0003)) h
theorem e24KC2ThetaAboveLeaf0003100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0003))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0003))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0003))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0003))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0003))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0003))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0003))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf0003113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0003))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0003))) h
theorem e24KC2ThetaAboveLeaf000312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0003)) = true := by
  have h : ((childHL (childLH thetaAboveCell0003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0003)) h
theorem e24KC2ThetaAboveLeaf000313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0003)) = true := by
  have h : ((childHH (childLH thetaAboveCell0003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0003)) h
theorem e24KC2ThetaAboveLeaf00032 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0003) = true := by
  have h : ((childHL thetaAboveCell0003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0003) h
theorem e24KC2ThetaAboveLeaf00033 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0003) = true := by
  have h : ((childHH thetaAboveCell0003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0003) h
theorem e24KC2ThetaAboveLeaf001000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0010)) = true := by
  have h : ((childLL (childLL thetaAboveCell0010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0010)) h
theorem e24KC2ThetaAboveLeaf001001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0010)) = true := by
  have h : ((childLH (childLL thetaAboveCell0010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0010)) h
theorem e24KC2ThetaAboveLeaf001002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0010)) = true := by
  have h : ((childHL (childLL thetaAboveCell0010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0010)) h
theorem e24KC2ThetaAboveLeaf001003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0010)) = true := by
  have h : ((childHH (childLL thetaAboveCell0010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0010)) h
theorem e24KC2ThetaAboveLeaf001010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0010)) = true := by
  have h : ((childLL (childLH thetaAboveCell0010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0010)) h
theorem e24KC2ThetaAboveLeaf001011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0010)) = true := by
  have h : ((childLH (childLH thetaAboveCell0010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0010)) h
theorem e24KC2ThetaAboveLeaf001012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0010)) = true := by
  have h : ((childHL (childLH thetaAboveCell0010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0010)) h
theorem e24KC2ThetaAboveLeaf001013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0010)) = true := by
  have h : ((childHH (childLH thetaAboveCell0010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0010)) h
theorem e24KC2ThetaAboveLeaf0010200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0010))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0010))) h
theorem e24KC2ThetaAboveLeaf0010201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0010))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0010))) h
theorem e24KC2ThetaAboveLeaf00102020 :
    adaptiveCoverCheck 11 thetaAboveCell00102020 = true := by
  have h : (thetaAboveCell00102020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102020 h
theorem e24KC2ThetaAboveLeaf00102021 :
    adaptiveCoverCheck 11 thetaAboveCell00102021 = true := by
  have h : (thetaAboveCell00102021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102021 h
theorem e24KC2ThetaAboveLeaf001020220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00102022) = true := by
  have h : ((childLL thetaAboveCell00102022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00102022) h
theorem e24KC2ThetaAboveLeaf001020221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00102022) = true := by
  have h : ((childLH thetaAboveCell00102022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00102022) h
theorem e24KC2ThetaAboveLeaf001020222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102022) = true := by
  have h : ((childHL thetaAboveCell00102022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102022) h
theorem e24KC2ThetaAboveLeaf001020223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102022) = true := by
  have h : ((childHH thetaAboveCell00102022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102022) h
theorem e24KC2ThetaAboveLeaf001020230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00102023) = true := by
  have h : ((childLL thetaAboveCell00102023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00102023) h
theorem e24KC2ThetaAboveLeaf001020231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00102023) = true := by
  have h : ((childLH thetaAboveCell00102023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00102023) h
theorem e24KC2ThetaAboveLeaf001020232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102023) = true := by
  have h : ((childHL thetaAboveCell00102023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102023) h
theorem e24KC2ThetaAboveLeaf001020233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102023) = true := by
  have h : ((childHH thetaAboveCell00102023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102023) h
theorem e24KC2ThetaAboveLeaf00102030 :
    adaptiveCoverCheck 11 thetaAboveCell00102030 = true := by
  have h : (thetaAboveCell00102030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102030 h
theorem e24KC2ThetaAboveLeaf00102031 :
    adaptiveCoverCheck 11 thetaAboveCell00102031 = true := by
  have h : (thetaAboveCell00102031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102031 h
theorem e24KC2ThetaAboveLeaf001020320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00102032) = true := by
  have h : ((childLL thetaAboveCell00102032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00102032) h
theorem e24KC2ThetaAboveLeaf001020321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00102032) = true := by
  have h : ((childLH thetaAboveCell00102032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00102032) h
theorem e24KC2ThetaAboveLeaf001020322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102032) = true := by
  have h : ((childHL thetaAboveCell00102032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102032) h
theorem e24KC2ThetaAboveLeaf001020323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102032) = true := by
  have h : ((childHH thetaAboveCell00102032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102032) h
theorem e24KC2ThetaAboveLeaf001020330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00102033) = true := by
  have h : ((childLL thetaAboveCell00102033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00102033) h
theorem e24KC2ThetaAboveLeaf001020331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00102033) = true := by
  have h : ((childLH thetaAboveCell00102033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00102033) h
theorem e24KC2ThetaAboveLeaf001020332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102033) = true := by
  have h : ((childHL thetaAboveCell00102033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102033) h
theorem e24KC2ThetaAboveLeaf001020333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102033) = true := by
  have h : ((childHH thetaAboveCell00102033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102033) h
theorem e24KC2ThetaAboveLeaf0010210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0010))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0010))) h
theorem e24KC2ThetaAboveLeaf0010211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0010))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0010))) h
theorem e24KC2ThetaAboveLeaf00102120 :
    adaptiveCoverCheck 11 thetaAboveCell00102120 = true := by
  have h : (thetaAboveCell00102120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102120 h
theorem e24KC2ThetaAboveLeaf00102121 :
    adaptiveCoverCheck 11 thetaAboveCell00102121 = true := by
  have h : (thetaAboveCell00102121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102121 h
theorem e24KC2ThetaAboveLeaf001021220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00102122) = true := by
  have h : ((childLL thetaAboveCell00102122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00102122) h
theorem e24KC2ThetaAboveLeaf001021221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00102122) = true := by
  have h : ((childLH thetaAboveCell00102122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00102122) h
theorem e24KC2ThetaAboveLeaf001021222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102122) = true := by
  have h : ((childHL thetaAboveCell00102122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102122) h
theorem e24KC2ThetaAboveLeaf001021223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102122) = true := by
  have h : ((childHH thetaAboveCell00102122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102122) h
theorem e24KC2ThetaAboveLeaf001021230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00102123) = true := by
  have h : ((childLL thetaAboveCell00102123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00102123) h
theorem e24KC2ThetaAboveLeaf001021231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00102123) = true := by
  have h : ((childLH thetaAboveCell00102123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00102123) h
theorem e24KC2ThetaAboveLeaf001021232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102123) = true := by
  have h : ((childHL thetaAboveCell00102123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102123) h
theorem e24KC2ThetaAboveLeaf001021233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102123) = true := by
  have h : ((childHH thetaAboveCell00102123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102123) h
theorem e24KC2ThetaAboveLeaf00102130 :
    adaptiveCoverCheck 11 thetaAboveCell00102130 = true := by
  have h : (thetaAboveCell00102130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102130 h
theorem e24KC2ThetaAboveLeaf00102131 :
    adaptiveCoverCheck 11 thetaAboveCell00102131 = true := by
  have h : (thetaAboveCell00102131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102131 h
theorem e24KC2ThetaAboveLeaf001021320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00102132) = true := by
  have h : ((childLL thetaAboveCell00102132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00102132) h
theorem e24KC2ThetaAboveLeaf001021321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00102132) = true := by
  have h : ((childLH thetaAboveCell00102132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00102132) h
theorem e24KC2ThetaAboveLeaf001021322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102132) = true := by
  have h : ((childHL thetaAboveCell00102132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102132) h
theorem e24KC2ThetaAboveLeaf001021323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102132) = true := by
  have h : ((childHH thetaAboveCell00102132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102132) h
theorem e24KC2ThetaAboveLeaf001021330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00102133) = true := by
  have h : ((childLL thetaAboveCell00102133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00102133) h
theorem e24KC2ThetaAboveLeaf001021331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00102133) = true := by
  have h : ((childLH thetaAboveCell00102133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00102133) h
theorem e24KC2ThetaAboveLeaf001021332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102133) = true := by
  have h : ((childHL thetaAboveCell00102133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102133) h
theorem e24KC2ThetaAboveLeaf001021333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102133) = true := by
  have h : ((childHH thetaAboveCell00102133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102133) h
theorem e24KC2ThetaAboveLeaf0010220000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102200)) = true := by
  have h : ((childLL (childLL thetaAboveCell00102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00102200)) h
theorem e24KC2ThetaAboveLeaf0010220001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102200)) = true := by
  have h : ((childLH (childLL thetaAboveCell00102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00102200)) h
theorem e24KC2ThetaAboveLeaf0010220002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102200)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102200)) h
theorem e24KC2ThetaAboveLeaf0010220003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102200)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102200)) h
theorem e24KC2ThetaAboveLeaf0010220010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102200)) = true := by
  have h : ((childLL (childLH thetaAboveCell00102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00102200)) h
theorem e24KC2ThetaAboveLeaf0010220011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102200)) = true := by
  have h : ((childLH (childLH thetaAboveCell00102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00102200)) h
theorem e24KC2ThetaAboveLeaf0010220012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102200)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102200)) h
theorem e24KC2ThetaAboveLeaf0010220013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102200)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102200)) h
theorem e24KC2ThetaAboveLeaf0010220100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102201)) = true := by
  have h : ((childLL (childLL thetaAboveCell00102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00102201)) h
theorem e24KC2ThetaAboveLeaf0010220101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102201)) = true := by
  have h : ((childLH (childLL thetaAboveCell00102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00102201)) h
theorem e24KC2ThetaAboveLeaf0010220102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102201)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102201)) h
theorem e24KC2ThetaAboveLeaf0010220103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102201)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102201)) h
theorem e24KC2ThetaAboveLeaf0010220110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102201)) = true := by
  have h : ((childLL (childLH thetaAboveCell00102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00102201)) h
theorem e24KC2ThetaAboveLeaf0010220111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102201)) = true := by
  have h : ((childLH (childLH thetaAboveCell00102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00102201)) h
theorem e24KC2ThetaAboveLeaf0010220112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102201)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102201)) h
theorem e24KC2ThetaAboveLeaf0010220113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102201)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102201)) h
theorem e24KC2ThetaAboveLeaf0010220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102202)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102202)) h
theorem e24KC2ThetaAboveLeaf0010220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102202)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102202)) h
theorem e24KC2ThetaAboveLeaf0010220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102202)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102202)) h
theorem e24KC2ThetaAboveLeaf0010220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102202)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102202)) h
theorem e24KC2ThetaAboveLeaf001022022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102202) = true := by
  have h : ((childHL thetaAboveCell00102202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102202) h
theorem e24KC2ThetaAboveLeaf001022023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102202) = true := by
  have h : ((childHH thetaAboveCell00102202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102202) h
theorem e24KC2ThetaAboveLeaf0010220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102203)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102203)) h
theorem e24KC2ThetaAboveLeaf0010220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102203)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102203)) h
theorem e24KC2ThetaAboveLeaf0010220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102203)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102203)) h
theorem e24KC2ThetaAboveLeaf0010220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102203)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102203)) h
theorem e24KC2ThetaAboveLeaf001022032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102203) = true := by
  have h : ((childHL thetaAboveCell00102203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102203) h
theorem e24KC2ThetaAboveLeaf001022033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102203) = true := by
  have h : ((childHH thetaAboveCell00102203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102203) h
theorem e24KC2ThetaAboveLeaf0010221000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102210)) = true := by
  have h : ((childLL (childLL thetaAboveCell00102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00102210)) h
theorem e24KC2ThetaAboveLeaf0010221001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102210)) = true := by
  have h : ((childLH (childLL thetaAboveCell00102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00102210)) h
theorem e24KC2ThetaAboveLeaf0010221002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102210)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102210)) h
theorem e24KC2ThetaAboveLeaf0010221003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102210)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102210)) h
theorem e24KC2ThetaAboveLeaf0010221010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102210)) = true := by
  have h : ((childLL (childLH thetaAboveCell00102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00102210)) h
theorem e24KC2ThetaAboveLeaf0010221011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102210)) = true := by
  have h : ((childLH (childLH thetaAboveCell00102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00102210)) h
theorem e24KC2ThetaAboveLeaf0010221012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102210)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102210)) h
theorem e24KC2ThetaAboveLeaf0010221013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102210)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102210)) h
theorem e24KC2ThetaAboveLeaf0010221100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102211)) = true := by
  have h : ((childLL (childLL thetaAboveCell00102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00102211)) h
theorem e24KC2ThetaAboveLeaf0010221101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102211)) = true := by
  have h : ((childLH (childLL thetaAboveCell00102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00102211)) h
theorem e24KC2ThetaAboveLeaf0010221102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102211)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102211)) h
theorem e24KC2ThetaAboveLeaf0010221103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102211)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102211)) h
theorem e24KC2ThetaAboveLeaf0010221110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102211)) = true := by
  have h : ((childLL (childLH thetaAboveCell00102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00102211)) h
theorem e24KC2ThetaAboveLeaf0010221111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102211)) = true := by
  have h : ((childLH (childLH thetaAboveCell00102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00102211)) h
theorem e24KC2ThetaAboveLeaf0010221112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102211)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102211)) h
theorem e24KC2ThetaAboveLeaf0010221113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102211)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102211)) h
theorem e24KC2ThetaAboveLeaf0010221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102212)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102212)) h
theorem e24KC2ThetaAboveLeaf0010221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102212)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102212)) h
theorem e24KC2ThetaAboveLeaf0010221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102212)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102212)) h
theorem e24KC2ThetaAboveLeaf0010221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102212)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102212)) h
theorem e24KC2ThetaAboveLeaf001022122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102212) = true := by
  have h : ((childHL thetaAboveCell00102212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102212) h
theorem e24KC2ThetaAboveLeaf001022123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102212) = true := by
  have h : ((childHH thetaAboveCell00102212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102212) h
theorem e24KC2ThetaAboveLeaf0010221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102213)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102213)) h
theorem e24KC2ThetaAboveLeaf0010221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102213)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102213)) h
theorem e24KC2ThetaAboveLeaf0010221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102213)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102213)) h
theorem e24KC2ThetaAboveLeaf0010221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102213)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102213)) h
theorem e24KC2ThetaAboveLeaf001022132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102213) = true := by
  have h : ((childHL thetaAboveCell00102213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102213) h
theorem e24KC2ThetaAboveLeaf001022133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102213) = true := by
  have h : ((childHH thetaAboveCell00102213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102213) h
theorem e24KC2ThetaAboveLeaf00102220 :
    adaptiveCoverCheck 11 thetaAboveCell00102220 = true := by
  have h : (thetaAboveCell00102220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102220 h
theorem e24KC2ThetaAboveLeaf00102221 :
    adaptiveCoverCheck 11 thetaAboveCell00102221 = true := by
  have h : (thetaAboveCell00102221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102221 h
theorem e24KC2ThetaAboveLeaf00102222 :
    adaptiveCoverCheck 11 thetaAboveCell00102222 = true := by
  have h : (thetaAboveCell00102222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102222 h
theorem e24KC2ThetaAboveLeaf00102223 :
    adaptiveCoverCheck 11 thetaAboveCell00102223 = true := by
  have h : (thetaAboveCell00102223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102223 h
theorem e24KC2ThetaAboveLeaf00102230 :
    adaptiveCoverCheck 11 thetaAboveCell00102230 = true := by
  have h : (thetaAboveCell00102230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102230 h
theorem e24KC2ThetaAboveLeaf00102231 :
    adaptiveCoverCheck 11 thetaAboveCell00102231 = true := by
  have h : (thetaAboveCell00102231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102231 h
theorem e24KC2ThetaAboveLeaf00102232 :
    adaptiveCoverCheck 11 thetaAboveCell00102232 = true := by
  have h : (thetaAboveCell00102232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102232 h
theorem e24KC2ThetaAboveLeaf00102233 :
    adaptiveCoverCheck 11 thetaAboveCell00102233 = true := by
  have h : (thetaAboveCell00102233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102233 h
theorem e24KC2ThetaAboveLeaf0010230000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102300)) = true := by
  have h : ((childLL (childLL thetaAboveCell00102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00102300)) h
theorem e24KC2ThetaAboveLeaf0010230001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102300)) = true := by
  have h : ((childLH (childLL thetaAboveCell00102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00102300)) h
theorem e24KC2ThetaAboveLeaf0010230002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102300)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102300)) h
theorem e24KC2ThetaAboveLeaf0010230003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102300)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102300)) h
theorem e24KC2ThetaAboveLeaf0010230010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102300)) = true := by
  have h : ((childLL (childLH thetaAboveCell00102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00102300)) h
theorem e24KC2ThetaAboveLeaf0010230011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102300)) = true := by
  have h : ((childLH (childLH thetaAboveCell00102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00102300)) h
theorem e24KC2ThetaAboveLeaf0010230012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102300)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102300)) h
theorem e24KC2ThetaAboveLeaf0010230013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102300)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102300)) h
theorem e24KC2ThetaAboveLeaf0010230100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102301)) = true := by
  have h : ((childLL (childLL thetaAboveCell00102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00102301)) h
theorem e24KC2ThetaAboveLeaf0010230101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102301)) = true := by
  have h : ((childLH (childLL thetaAboveCell00102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00102301)) h
theorem e24KC2ThetaAboveLeaf0010230102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102301)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102301)) h
theorem e24KC2ThetaAboveLeaf0010230103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102301)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102301)) h
theorem e24KC2ThetaAboveLeaf0010230110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102301)) = true := by
  have h : ((childLL (childLH thetaAboveCell00102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00102301)) h
theorem e24KC2ThetaAboveLeaf0010230111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102301)) = true := by
  have h : ((childLH (childLH thetaAboveCell00102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00102301)) h
theorem e24KC2ThetaAboveLeaf0010230112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102301)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102301)) h
theorem e24KC2ThetaAboveLeaf0010230113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102301)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102301)) h
theorem e24KC2ThetaAboveLeaf0010230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102302)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102302)) h
theorem e24KC2ThetaAboveLeaf0010230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102302)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102302)) h
theorem e24KC2ThetaAboveLeaf0010230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102302)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102302)) h
theorem e24KC2ThetaAboveLeaf0010230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102302)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102302)) h
theorem e24KC2ThetaAboveLeaf001023022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102302) = true := by
  have h : ((childHL thetaAboveCell00102302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102302) h
theorem e24KC2ThetaAboveLeaf001023023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102302) = true := by
  have h : ((childHH thetaAboveCell00102302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102302) h
theorem e24KC2ThetaAboveLeaf0010230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102303)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102303)) h
theorem e24KC2ThetaAboveLeaf0010230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102303)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102303)) h
theorem e24KC2ThetaAboveLeaf0010230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102303)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102303)) h
theorem e24KC2ThetaAboveLeaf0010230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102303)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102303)) h
theorem e24KC2ThetaAboveLeaf001023032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102303) = true := by
  have h : ((childHL thetaAboveCell00102303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102303) h
theorem e24KC2ThetaAboveLeaf001023033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102303) = true := by
  have h : ((childHH thetaAboveCell00102303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102303) h
theorem e24KC2ThetaAboveLeaf0010231000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102310)) = true := by
  have h : ((childLL (childLL thetaAboveCell00102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00102310)) h
theorem e24KC2ThetaAboveLeaf0010231001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102310)) = true := by
  have h : ((childLH (childLL thetaAboveCell00102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00102310)) h
theorem e24KC2ThetaAboveLeaf0010231002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102310)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102310)) h
theorem e24KC2ThetaAboveLeaf0010231003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102310)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102310)) h
theorem e24KC2ThetaAboveLeaf0010231010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102310)) = true := by
  have h : ((childLL (childLH thetaAboveCell00102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00102310)) h
theorem e24KC2ThetaAboveLeaf0010231011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102310)) = true := by
  have h : ((childLH (childLH thetaAboveCell00102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00102310)) h
theorem e24KC2ThetaAboveLeaf0010231012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102310)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102310)) h
theorem e24KC2ThetaAboveLeaf0010231013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102310)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102310)) h
theorem e24KC2ThetaAboveLeaf0010231100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102311)) = true := by
  have h : ((childLL (childLL thetaAboveCell00102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00102311)) h
theorem e24KC2ThetaAboveLeaf0010231101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102311)) = true := by
  have h : ((childLH (childLL thetaAboveCell00102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00102311)) h
theorem e24KC2ThetaAboveLeaf0010231102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102311)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102311)) h
theorem e24KC2ThetaAboveLeaf0010231103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102311)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102311)) h
theorem e24KC2ThetaAboveLeaf0010231110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102311)) = true := by
  have h : ((childLL (childLH thetaAboveCell00102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00102311)) h
theorem e24KC2ThetaAboveLeaf0010231111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102311)) = true := by
  have h : ((childLH (childLH thetaAboveCell00102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00102311)) h
theorem e24KC2ThetaAboveLeaf0010231112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102311)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102311)) h
theorem e24KC2ThetaAboveLeaf0010231113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102311)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102311)) h
theorem e24KC2ThetaAboveLeaf0010231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102312)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102312)) h
theorem e24KC2ThetaAboveLeaf0010231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102312)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102312)) h
theorem e24KC2ThetaAboveLeaf0010231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102312)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102312)) h
theorem e24KC2ThetaAboveLeaf0010231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102312)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102312)) h
theorem e24KC2ThetaAboveLeaf001023122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102312) = true := by
  have h : ((childHL thetaAboveCell00102312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102312) h
theorem e24KC2ThetaAboveLeaf001023123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102312) = true := by
  have h : ((childHH thetaAboveCell00102312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102312) h
theorem e24KC2ThetaAboveLeaf0010231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00102313)) = true := by
  have h : ((childHL (childLL thetaAboveCell00102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00102313)) h
theorem e24KC2ThetaAboveLeaf0010231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00102313)) = true := by
  have h : ((childHH (childLL thetaAboveCell00102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00102313)) h
theorem e24KC2ThetaAboveLeaf0010231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00102313)) = true := by
  have h : ((childHL (childLH thetaAboveCell00102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00102313)) h
theorem e24KC2ThetaAboveLeaf0010231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00102313)) = true := by
  have h : ((childHH (childLH thetaAboveCell00102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00102313)) h
theorem e24KC2ThetaAboveLeaf001023132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00102313) = true := by
  have h : ((childHL thetaAboveCell00102313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00102313) h
theorem e24KC2ThetaAboveLeaf001023133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00102313) = true := by
  have h : ((childHH thetaAboveCell00102313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00102313) h
theorem e24KC2ThetaAboveLeaf00102320 :
    adaptiveCoverCheck 11 thetaAboveCell00102320 = true := by
  have h : (thetaAboveCell00102320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102320 h
theorem e24KC2ThetaAboveLeaf00102321 :
    adaptiveCoverCheck 11 thetaAboveCell00102321 = true := by
  have h : (thetaAboveCell00102321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102321 h
theorem e24KC2ThetaAboveLeaf00102322 :
    adaptiveCoverCheck 11 thetaAboveCell00102322 = true := by
  have h : (thetaAboveCell00102322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102322 h
theorem e24KC2ThetaAboveLeaf00102323 :
    adaptiveCoverCheck 11 thetaAboveCell00102323 = true := by
  have h : (thetaAboveCell00102323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102323 h
theorem e24KC2ThetaAboveLeaf00102330 :
    adaptiveCoverCheck 11 thetaAboveCell00102330 = true := by
  have h : (thetaAboveCell00102330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102330 h
theorem e24KC2ThetaAboveLeaf00102331 :
    adaptiveCoverCheck 11 thetaAboveCell00102331 = true := by
  have h : (thetaAboveCell00102331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102331 h
theorem e24KC2ThetaAboveLeaf00102332 :
    adaptiveCoverCheck 11 thetaAboveCell00102332 = true := by
  have h : (thetaAboveCell00102332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102332 h
theorem e24KC2ThetaAboveLeaf00102333 :
    adaptiveCoverCheck 11 thetaAboveCell00102333 = true := by
  have h : (thetaAboveCell00102333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00102333 h
theorem e24KC2ThetaAboveLeaf0010300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0010))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0010))) h
theorem e24KC2ThetaAboveLeaf0010301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0010))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0010))) h
theorem e24KC2ThetaAboveLeaf00103020 :
    adaptiveCoverCheck 11 thetaAboveCell00103020 = true := by
  have h : (thetaAboveCell00103020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103020 h
theorem e24KC2ThetaAboveLeaf00103021 :
    adaptiveCoverCheck 11 thetaAboveCell00103021 = true := by
  have h : (thetaAboveCell00103021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103021 h
theorem e24KC2ThetaAboveLeaf00103022 :
    adaptiveCoverCheck 11 thetaAboveCell00103022 = true := by
  have h : (thetaAboveCell00103022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103022 h
theorem e24KC2ThetaAboveLeaf00103023 :
    adaptiveCoverCheck 11 thetaAboveCell00103023 = true := by
  have h : (thetaAboveCell00103023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103023 h
theorem e24KC2ThetaAboveLeaf00103030 :
    adaptiveCoverCheck 11 thetaAboveCell00103030 = true := by
  have h : (thetaAboveCell00103030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103030 h
theorem e24KC2ThetaAboveLeaf00103031 :
    adaptiveCoverCheck 11 thetaAboveCell00103031 = true := by
  have h : (thetaAboveCell00103031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103031 h
theorem e24KC2ThetaAboveLeaf00103032 :
    adaptiveCoverCheck 11 thetaAboveCell00103032 = true := by
  have h : (thetaAboveCell00103032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103032 h
theorem e24KC2ThetaAboveLeaf00103033 :
    adaptiveCoverCheck 11 thetaAboveCell00103033 = true := by
  have h : (thetaAboveCell00103033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103033 h
theorem e24KC2ThetaAboveLeaf0010310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0010))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0010))) h
theorem e24KC2ThetaAboveLeaf0010311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0010))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0010))) h
theorem e24KC2ThetaAboveLeaf00103120 :
    adaptiveCoverCheck 11 thetaAboveCell00103120 = true := by
  have h : (thetaAboveCell00103120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103120 h
theorem e24KC2ThetaAboveLeaf00103121 :
    adaptiveCoverCheck 11 thetaAboveCell00103121 = true := by
  have h : (thetaAboveCell00103121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103121 h
theorem e24KC2ThetaAboveLeaf00103122 :
    adaptiveCoverCheck 11 thetaAboveCell00103122 = true := by
  have h : (thetaAboveCell00103122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103122 h
theorem e24KC2ThetaAboveLeaf00103123 :
    adaptiveCoverCheck 11 thetaAboveCell00103123 = true := by
  have h : (thetaAboveCell00103123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103123 h
theorem e24KC2ThetaAboveLeaf00103130 :
    adaptiveCoverCheck 11 thetaAboveCell00103130 = true := by
  have h : (thetaAboveCell00103130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103130 h
theorem e24KC2ThetaAboveLeaf00103131 :
    adaptiveCoverCheck 11 thetaAboveCell00103131 = true := by
  have h : (thetaAboveCell00103131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103131 h
theorem e24KC2ThetaAboveLeaf00103132 :
    adaptiveCoverCheck 11 thetaAboveCell00103132 = true := by
  have h : (thetaAboveCell00103132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103132 h
theorem e24KC2ThetaAboveLeaf00103133 :
    adaptiveCoverCheck 11 thetaAboveCell00103133 = true := by
  have h : (thetaAboveCell00103133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103133 h
theorem e24KC2ThetaAboveLeaf0010320000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103200)) = true := by
  have h : ((childLL (childLL thetaAboveCell00103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00103200)) h
theorem e24KC2ThetaAboveLeaf0010320001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103200)) = true := by
  have h : ((childLH (childLL thetaAboveCell00103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00103200)) h
theorem e24KC2ThetaAboveLeaf0010320002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103200)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103200)) h
theorem e24KC2ThetaAboveLeaf0010320003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103200)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103200)) h
theorem e24KC2ThetaAboveLeaf0010320010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103200)) = true := by
  have h : ((childLL (childLH thetaAboveCell00103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00103200)) h
theorem e24KC2ThetaAboveLeaf0010320011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103200)) = true := by
  have h : ((childLH (childLH thetaAboveCell00103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00103200)) h
theorem e24KC2ThetaAboveLeaf0010320012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103200)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103200)) h
theorem e24KC2ThetaAboveLeaf0010320013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103200)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103200)) h
theorem e24KC2ThetaAboveLeaf0010320100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103201)) = true := by
  have h : ((childLL (childLL thetaAboveCell00103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00103201)) h
theorem e24KC2ThetaAboveLeaf0010320101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103201)) = true := by
  have h : ((childLH (childLL thetaAboveCell00103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00103201)) h
theorem e24KC2ThetaAboveLeaf0010320102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103201)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103201)) h
theorem e24KC2ThetaAboveLeaf0010320103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103201)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103201)) h
theorem e24KC2ThetaAboveLeaf0010320110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103201)) = true := by
  have h : ((childLL (childLH thetaAboveCell00103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00103201)) h
theorem e24KC2ThetaAboveLeaf0010320111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103201)) = true := by
  have h : ((childLH (childLH thetaAboveCell00103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00103201)) h
theorem e24KC2ThetaAboveLeaf0010320112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103201)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103201)) h
theorem e24KC2ThetaAboveLeaf0010320113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103201)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103201)) h
theorem e24KC2ThetaAboveLeaf0010320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103202)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103202)) h
theorem e24KC2ThetaAboveLeaf0010320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103202)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103202)) h
theorem e24KC2ThetaAboveLeaf0010320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103202)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103202)) h
theorem e24KC2ThetaAboveLeaf0010320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103202)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103202)) h
theorem e24KC2ThetaAboveLeaf001032022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00103202) = true := by
  have h : ((childHL thetaAboveCell00103202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00103202) h
theorem e24KC2ThetaAboveLeaf001032023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00103202) = true := by
  have h : ((childHH thetaAboveCell00103202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00103202) h
theorem e24KC2ThetaAboveLeaf0010320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103203)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103203)) h
theorem e24KC2ThetaAboveLeaf0010320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103203)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103203)) h
theorem e24KC2ThetaAboveLeaf0010320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103203)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103203)) h
theorem e24KC2ThetaAboveLeaf0010320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103203)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103203)) h
theorem e24KC2ThetaAboveLeaf001032032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00103203) = true := by
  have h : ((childHL thetaAboveCell00103203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00103203) h
theorem e24KC2ThetaAboveLeaf001032033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00103203) = true := by
  have h : ((childHH thetaAboveCell00103203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00103203) h
theorem e24KC2ThetaAboveLeaf0010321000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103210)) = true := by
  have h : ((childLL (childLL thetaAboveCell00103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00103210)) h
theorem e24KC2ThetaAboveLeaf0010321001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103210)) = true := by
  have h : ((childLH (childLL thetaAboveCell00103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00103210)) h
theorem e24KC2ThetaAboveLeaf0010321002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103210)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103210)) h
theorem e24KC2ThetaAboveLeaf0010321003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103210)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103210)) h
theorem e24KC2ThetaAboveLeaf0010321010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103210)) = true := by
  have h : ((childLL (childLH thetaAboveCell00103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00103210)) h
theorem e24KC2ThetaAboveLeaf0010321011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103210)) = true := by
  have h : ((childLH (childLH thetaAboveCell00103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00103210)) h
theorem e24KC2ThetaAboveLeaf0010321012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103210)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103210)) h
theorem e24KC2ThetaAboveLeaf0010321013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103210)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103210)) h
theorem e24KC2ThetaAboveLeaf0010321100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103211)) = true := by
  have h : ((childLL (childLL thetaAboveCell00103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00103211)) h
theorem e24KC2ThetaAboveLeaf0010321101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103211)) = true := by
  have h : ((childLH (childLL thetaAboveCell00103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00103211)) h
theorem e24KC2ThetaAboveLeaf0010321102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103211)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103211)) h
theorem e24KC2ThetaAboveLeaf0010321103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103211)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103211)) h
theorem e24KC2ThetaAboveLeaf0010321110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103211)) = true := by
  have h : ((childLL (childLH thetaAboveCell00103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00103211)) h
theorem e24KC2ThetaAboveLeaf0010321111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103211)) = true := by
  have h : ((childLH (childLH thetaAboveCell00103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00103211)) h
theorem e24KC2ThetaAboveLeaf0010321112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103211)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103211)) h
theorem e24KC2ThetaAboveLeaf0010321113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103211)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103211)) h
theorem e24KC2ThetaAboveLeaf0010321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103212)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103212)) h
theorem e24KC2ThetaAboveLeaf0010321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103212)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103212)) h
theorem e24KC2ThetaAboveLeaf0010321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103212)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103212)) h
theorem e24KC2ThetaAboveLeaf0010321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103212)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103212)) h
theorem e24KC2ThetaAboveLeaf001032122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00103212) = true := by
  have h : ((childHL thetaAboveCell00103212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00103212) h
theorem e24KC2ThetaAboveLeaf001032123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00103212) = true := by
  have h : ((childHH thetaAboveCell00103212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00103212) h
theorem e24KC2ThetaAboveLeaf0010321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103213)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103213)) h
theorem e24KC2ThetaAboveLeaf0010321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103213)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103213)) h
theorem e24KC2ThetaAboveLeaf0010321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103213)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103213)) h
theorem e24KC2ThetaAboveLeaf0010321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103213)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103213)) h
theorem e24KC2ThetaAboveLeaf001032132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00103213) = true := by
  have h : ((childHL thetaAboveCell00103213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00103213) h
theorem e24KC2ThetaAboveLeaf001032133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00103213) = true := by
  have h : ((childHH thetaAboveCell00103213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00103213) h
theorem e24KC2ThetaAboveLeaf00103220 :
    adaptiveCoverCheck 11 thetaAboveCell00103220 = true := by
  have h : (thetaAboveCell00103220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103220 h
theorem e24KC2ThetaAboveLeaf00103221 :
    adaptiveCoverCheck 11 thetaAboveCell00103221 = true := by
  have h : (thetaAboveCell00103221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103221 h
theorem e24KC2ThetaAboveLeaf00103222 :
    adaptiveCoverCheck 11 thetaAboveCell00103222 = true := by
  have h : (thetaAboveCell00103222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103222 h
theorem e24KC2ThetaAboveLeaf00103223 :
    adaptiveCoverCheck 11 thetaAboveCell00103223 = true := by
  have h : (thetaAboveCell00103223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103223 h
theorem e24KC2ThetaAboveLeaf00103230 :
    adaptiveCoverCheck 11 thetaAboveCell00103230 = true := by
  have h : (thetaAboveCell00103230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103230 h
theorem e24KC2ThetaAboveLeaf00103231 :
    adaptiveCoverCheck 11 thetaAboveCell00103231 = true := by
  have h : (thetaAboveCell00103231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103231 h
theorem e24KC2ThetaAboveLeaf00103232 :
    adaptiveCoverCheck 11 thetaAboveCell00103232 = true := by
  have h : (thetaAboveCell00103232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103232 h
theorem e24KC2ThetaAboveLeaf00103233 :
    adaptiveCoverCheck 11 thetaAboveCell00103233 = true := by
  have h : (thetaAboveCell00103233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103233 h
theorem e24KC2ThetaAboveLeaf0010330000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103300)) = true := by
  have h : ((childLL (childLL thetaAboveCell00103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00103300)) h
theorem e24KC2ThetaAboveLeaf0010330001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103300)) = true := by
  have h : ((childLH (childLL thetaAboveCell00103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00103300)) h
theorem e24KC2ThetaAboveLeaf0010330002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103300)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103300)) h
theorem e24KC2ThetaAboveLeaf0010330003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103300)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103300)) h
theorem e24KC2ThetaAboveLeaf0010330010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103300)) = true := by
  have h : ((childLL (childLH thetaAboveCell00103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00103300)) h
theorem e24KC2ThetaAboveLeaf0010330011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103300)) = true := by
  have h : ((childLH (childLH thetaAboveCell00103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00103300)) h
theorem e24KC2ThetaAboveLeaf0010330012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103300)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103300)) h
theorem e24KC2ThetaAboveLeaf0010330013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103300)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103300)) h
theorem e24KC2ThetaAboveLeaf0010330100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103301)) = true := by
  have h : ((childLL (childLL thetaAboveCell00103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00103301)) h
theorem e24KC2ThetaAboveLeaf0010330101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103301)) = true := by
  have h : ((childLH (childLL thetaAboveCell00103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00103301)) h
theorem e24KC2ThetaAboveLeaf0010330102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103301)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103301)) h
theorem e24KC2ThetaAboveLeaf0010330103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103301)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103301)) h
theorem e24KC2ThetaAboveLeaf0010330110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103301)) = true := by
  have h : ((childLL (childLH thetaAboveCell00103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00103301)) h
theorem e24KC2ThetaAboveLeaf0010330111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103301)) = true := by
  have h : ((childLH (childLH thetaAboveCell00103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00103301)) h
theorem e24KC2ThetaAboveLeaf0010330112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103301)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103301)) h
theorem e24KC2ThetaAboveLeaf0010330113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103301)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103301)) h
theorem e24KC2ThetaAboveLeaf0010330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103302)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103302)) h
theorem e24KC2ThetaAboveLeaf0010330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103302)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103302)) h
theorem e24KC2ThetaAboveLeaf0010330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103302)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103302)) h
theorem e24KC2ThetaAboveLeaf0010330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103302)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103302)) h
theorem e24KC2ThetaAboveLeaf001033022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00103302) = true := by
  have h : ((childHL thetaAboveCell00103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00103302) h
theorem e24KC2ThetaAboveLeaf001033023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00103302) = true := by
  have h : ((childHH thetaAboveCell00103302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00103302) h
theorem e24KC2ThetaAboveLeaf0010330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103303)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103303)) h
theorem e24KC2ThetaAboveLeaf0010330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103303)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103303)) h
theorem e24KC2ThetaAboveLeaf0010330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103303)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103303)) h
theorem e24KC2ThetaAboveLeaf0010330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103303)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103303)) h
theorem e24KC2ThetaAboveLeaf001033032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00103303) = true := by
  have h : ((childHL thetaAboveCell00103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00103303) h
theorem e24KC2ThetaAboveLeaf001033033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00103303) = true := by
  have h : ((childHH thetaAboveCell00103303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00103303) h
theorem e24KC2ThetaAboveLeaf0010331000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103310)) = true := by
  have h : ((childLL (childLL thetaAboveCell00103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00103310)) h
theorem e24KC2ThetaAboveLeaf0010331001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103310)) = true := by
  have h : ((childLH (childLL thetaAboveCell00103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00103310)) h
theorem e24KC2ThetaAboveLeaf0010331002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103310)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103310)) h
theorem e24KC2ThetaAboveLeaf0010331003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103310)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103310)) h
theorem e24KC2ThetaAboveLeaf0010331010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103310)) = true := by
  have h : ((childLL (childLH thetaAboveCell00103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00103310)) h
theorem e24KC2ThetaAboveLeaf0010331011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103310)) = true := by
  have h : ((childLH (childLH thetaAboveCell00103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00103310)) h
theorem e24KC2ThetaAboveLeaf0010331012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103310)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103310)) h
theorem e24KC2ThetaAboveLeaf0010331013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103310)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103310)) h
theorem e24KC2ThetaAboveLeaf0010331100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103311)) = true := by
  have h : ((childLL (childLL thetaAboveCell00103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00103311)) h
theorem e24KC2ThetaAboveLeaf0010331101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103311)) = true := by
  have h : ((childLH (childLL thetaAboveCell00103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00103311)) h
theorem e24KC2ThetaAboveLeaf0010331102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103311)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103311)) h
theorem e24KC2ThetaAboveLeaf0010331103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103311)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103311)) h
theorem e24KC2ThetaAboveLeaf0010331110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103311)) = true := by
  have h : ((childLL (childLH thetaAboveCell00103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00103311)) h
theorem e24KC2ThetaAboveLeaf0010331111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103311)) = true := by
  have h : ((childLH (childLH thetaAboveCell00103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00103311)) h
theorem e24KC2ThetaAboveLeaf0010331112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103311)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103311)) h
theorem e24KC2ThetaAboveLeaf0010331113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103311)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103311)) h
theorem e24KC2ThetaAboveLeaf0010331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103312)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103312)) h
theorem e24KC2ThetaAboveLeaf0010331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103312)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103312)) h
theorem e24KC2ThetaAboveLeaf0010331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103312)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103312)) h
theorem e24KC2ThetaAboveLeaf0010331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103312)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103312)) h
theorem e24KC2ThetaAboveLeaf001033122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00103312) = true := by
  have h : ((childHL thetaAboveCell00103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00103312) h
theorem e24KC2ThetaAboveLeaf001033123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00103312) = true := by
  have h : ((childHH thetaAboveCell00103312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00103312) h
theorem e24KC2ThetaAboveLeaf0010331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00103313)) = true := by
  have h : ((childHL (childLL thetaAboveCell00103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00103313)) h
theorem e24KC2ThetaAboveLeaf0010331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00103313)) = true := by
  have h : ((childHH (childLL thetaAboveCell00103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00103313)) h
theorem e24KC2ThetaAboveLeaf0010331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00103313)) = true := by
  have h : ((childHL (childLH thetaAboveCell00103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00103313)) h
theorem e24KC2ThetaAboveLeaf0010331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00103313)) = true := by
  have h : ((childHH (childLH thetaAboveCell00103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00103313)) h
theorem e24KC2ThetaAboveLeaf001033132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00103313) = true := by
  have h : ((childHL thetaAboveCell00103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00103313) h
theorem e24KC2ThetaAboveLeaf001033133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00103313) = true := by
  have h : ((childHH thetaAboveCell00103313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00103313) h
theorem e24KC2ThetaAboveLeaf00103320 :
    adaptiveCoverCheck 11 thetaAboveCell00103320 = true := by
  have h : (thetaAboveCell00103320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103320 h
theorem e24KC2ThetaAboveLeaf00103321 :
    adaptiveCoverCheck 11 thetaAboveCell00103321 = true := by
  have h : (thetaAboveCell00103321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103321 h
theorem e24KC2ThetaAboveLeaf00103322 :
    adaptiveCoverCheck 11 thetaAboveCell00103322 = true := by
  have h : (thetaAboveCell00103322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103322 h
theorem e24KC2ThetaAboveLeaf00103323 :
    adaptiveCoverCheck 11 thetaAboveCell00103323 = true := by
  have h : (thetaAboveCell00103323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103323 h
theorem e24KC2ThetaAboveLeaf00103330 :
    adaptiveCoverCheck 11 thetaAboveCell00103330 = true := by
  have h : (thetaAboveCell00103330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103330 h
theorem e24KC2ThetaAboveLeaf00103331 :
    adaptiveCoverCheck 11 thetaAboveCell00103331 = true := by
  have h : (thetaAboveCell00103331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103331 h
theorem e24KC2ThetaAboveLeaf00103332 :
    adaptiveCoverCheck 11 thetaAboveCell00103332 = true := by
  have h : (thetaAboveCell00103332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103332 h
theorem e24KC2ThetaAboveLeaf00103333 :
    adaptiveCoverCheck 11 thetaAboveCell00103333 = true := by
  have h : (thetaAboveCell00103333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00103333 h
theorem e24KC2ThetaAboveLeaf001100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0011)) = true := by
  have h : ((childLL (childLL thetaAboveCell0011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0011)) h
theorem e24KC2ThetaAboveLeaf001101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0011)) = true := by
  have h : ((childLH (childLL thetaAboveCell0011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0011)) h
theorem e24KC2ThetaAboveLeaf001102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0011)) = true := by
  have h : ((childHL (childLL thetaAboveCell0011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0011)) h
theorem e24KC2ThetaAboveLeaf001103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0011)) = true := by
  have h : ((childHH (childLL thetaAboveCell0011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0011)) h
theorem e24KC2ThetaAboveLeaf001110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0011)) = true := by
  have h : ((childLL (childLH thetaAboveCell0011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0011)) h
theorem e24KC2ThetaAboveLeaf001111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0011)) = true := by
  have h : ((childLH (childLH thetaAboveCell0011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0011)) h
theorem e24KC2ThetaAboveLeaf001112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0011)) = true := by
  have h : ((childHL (childLH thetaAboveCell0011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0011)) h
theorem e24KC2ThetaAboveLeaf001113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0011)) = true := by
  have h : ((childHH (childLH thetaAboveCell0011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0011)) h
theorem e24KC2ThetaAboveLeaf0011200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0011))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0011))) h
theorem e24KC2ThetaAboveLeaf0011201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0011))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0011))) h
theorem e24KC2ThetaAboveLeaf00112020 :
    adaptiveCoverCheck 11 thetaAboveCell00112020 = true := by
  have h : (thetaAboveCell00112020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112020 h
theorem e24KC2ThetaAboveLeaf00112021 :
    adaptiveCoverCheck 11 thetaAboveCell00112021 = true := by
  have h : (thetaAboveCell00112021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112021 h
theorem e24KC2ThetaAboveLeaf00112022 :
    adaptiveCoverCheck 11 thetaAboveCell00112022 = true := by
  have h : (thetaAboveCell00112022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112022 h
theorem e24KC2ThetaAboveLeaf00112023 :
    adaptiveCoverCheck 11 thetaAboveCell00112023 = true := by
  have h : (thetaAboveCell00112023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112023 h
theorem e24KC2ThetaAboveLeaf00112030 :
    adaptiveCoverCheck 11 thetaAboveCell00112030 = true := by
  have h : (thetaAboveCell00112030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112030 h
theorem e24KC2ThetaAboveLeaf00112031 :
    adaptiveCoverCheck 11 thetaAboveCell00112031 = true := by
  have h : (thetaAboveCell00112031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112031 h
theorem e24KC2ThetaAboveLeaf00112032 :
    adaptiveCoverCheck 11 thetaAboveCell00112032 = true := by
  have h : (thetaAboveCell00112032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112032 h
theorem e24KC2ThetaAboveLeaf00112033 :
    adaptiveCoverCheck 11 thetaAboveCell00112033 = true := by
  have h : (thetaAboveCell00112033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112033 h
theorem e24KC2ThetaAboveLeaf0011210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0011))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0011))) h
theorem e24KC2ThetaAboveLeaf0011211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0011))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0011))) h
theorem e24KC2ThetaAboveLeaf00112120 :
    adaptiveCoverCheck 11 thetaAboveCell00112120 = true := by
  have h : (thetaAboveCell00112120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112120 h
theorem e24KC2ThetaAboveLeaf00112121 :
    adaptiveCoverCheck 11 thetaAboveCell00112121 = true := by
  have h : (thetaAboveCell00112121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112121 h
theorem e24KC2ThetaAboveLeaf00112122 :
    adaptiveCoverCheck 11 thetaAboveCell00112122 = true := by
  have h : (thetaAboveCell00112122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112122 h
theorem e24KC2ThetaAboveLeaf00112123 :
    adaptiveCoverCheck 11 thetaAboveCell00112123 = true := by
  have h : (thetaAboveCell00112123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112123 h
theorem e24KC2ThetaAboveLeaf00112130 :
    adaptiveCoverCheck 11 thetaAboveCell00112130 = true := by
  have h : (thetaAboveCell00112130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112130 h
theorem e24KC2ThetaAboveLeaf00112131 :
    adaptiveCoverCheck 11 thetaAboveCell00112131 = true := by
  have h : (thetaAboveCell00112131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112131 h
theorem e24KC2ThetaAboveLeaf00112132 :
    adaptiveCoverCheck 11 thetaAboveCell00112132 = true := by
  have h : (thetaAboveCell00112132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112132 h
theorem e24KC2ThetaAboveLeaf00112133 :
    adaptiveCoverCheck 11 thetaAboveCell00112133 = true := by
  have h : (thetaAboveCell00112133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112133 h
theorem e24KC2ThetaAboveLeaf0011220000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112200)) = true := by
  have h : ((childLL (childLL thetaAboveCell00112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00112200)) h
theorem e24KC2ThetaAboveLeaf0011220001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112200)) = true := by
  have h : ((childLH (childLL thetaAboveCell00112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00112200)) h
theorem e24KC2ThetaAboveLeaf0011220002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112200)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112200)) h
theorem e24KC2ThetaAboveLeaf0011220003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112200)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112200)) h
theorem e24KC2ThetaAboveLeaf0011220010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112200)) = true := by
  have h : ((childLL (childLH thetaAboveCell00112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00112200)) h
theorem e24KC2ThetaAboveLeaf0011220011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112200)) = true := by
  have h : ((childLH (childLH thetaAboveCell00112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00112200)) h
theorem e24KC2ThetaAboveLeaf0011220012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112200)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112200)) h
theorem e24KC2ThetaAboveLeaf0011220013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112200)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112200)) h
theorem e24KC2ThetaAboveLeaf0011220100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112201)) = true := by
  have h : ((childLL (childLL thetaAboveCell00112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00112201)) h
theorem e24KC2ThetaAboveLeaf0011220101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112201)) = true := by
  have h : ((childLH (childLL thetaAboveCell00112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00112201)) h
theorem e24KC2ThetaAboveLeaf0011220102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112201)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112201)) h
theorem e24KC2ThetaAboveLeaf0011220103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112201)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112201)) h
theorem e24KC2ThetaAboveLeaf0011220110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112201)) = true := by
  have h : ((childLL (childLH thetaAboveCell00112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00112201)) h
theorem e24KC2ThetaAboveLeaf0011220111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112201)) = true := by
  have h : ((childLH (childLH thetaAboveCell00112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00112201)) h
theorem e24KC2ThetaAboveLeaf0011220112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112201)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112201)) h
theorem e24KC2ThetaAboveLeaf0011220113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112201)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112201)) h
theorem e24KC2ThetaAboveLeaf0011220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112202)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112202)) h
theorem e24KC2ThetaAboveLeaf0011220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112202)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112202)) h
theorem e24KC2ThetaAboveLeaf0011220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112202)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112202)) h
theorem e24KC2ThetaAboveLeaf0011220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112202)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112202)) h
theorem e24KC2ThetaAboveLeaf001122022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00112202) = true := by
  have h : ((childHL thetaAboveCell00112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00112202) h
theorem e24KC2ThetaAboveLeaf001122023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00112202) = true := by
  have h : ((childHH thetaAboveCell00112202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00112202) h
theorem e24KC2ThetaAboveLeaf0011220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112203)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112203)) h
theorem e24KC2ThetaAboveLeaf0011220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112203)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112203)) h
theorem e24KC2ThetaAboveLeaf0011220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112203)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112203)) h
theorem e24KC2ThetaAboveLeaf0011220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112203)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112203)) h
theorem e24KC2ThetaAboveLeaf001122032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00112203) = true := by
  have h : ((childHL thetaAboveCell00112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00112203) h
theorem e24KC2ThetaAboveLeaf001122033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00112203) = true := by
  have h : ((childHH thetaAboveCell00112203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00112203) h
theorem e24KC2ThetaAboveLeaf0011221000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112210)) = true := by
  have h : ((childLL (childLL thetaAboveCell00112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00112210)) h
theorem e24KC2ThetaAboveLeaf0011221001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112210)) = true := by
  have h : ((childLH (childLL thetaAboveCell00112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00112210)) h
theorem e24KC2ThetaAboveLeaf0011221002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112210)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112210)) h
theorem e24KC2ThetaAboveLeaf0011221003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112210)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112210)) h
theorem e24KC2ThetaAboveLeaf001122101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00112210) = true := by
  have h : ((childLH thetaAboveCell00112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00112210) h
theorem e24KC2ThetaAboveLeaf001122110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00112211) = true := by
  have h : ((childLL thetaAboveCell00112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00112211) h
theorem e24KC2ThetaAboveLeaf001122111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00112211) = true := by
  have h : ((childLH thetaAboveCell00112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00112211) h
theorem e24KC2ThetaAboveLeaf0011221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112212)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112212)) h
theorem e24KC2ThetaAboveLeaf0011221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112212)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112212)) h
theorem e24KC2ThetaAboveLeaf0011221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112212)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112212)) h
theorem e24KC2ThetaAboveLeaf0011221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112212)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112212)) h
theorem e24KC2ThetaAboveLeaf001122122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00112212) = true := by
  have h : ((childHL thetaAboveCell00112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00112212) h
theorem e24KC2ThetaAboveLeaf001122123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00112212) = true := by
  have h : ((childHH thetaAboveCell00112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00112212) h
theorem e24KC2ThetaAboveLeaf0011221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112213)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112213)) h
theorem e24KC2ThetaAboveLeaf0011221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112213)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112213)) h
theorem e24KC2ThetaAboveLeaf0011221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112213)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112213)) h
theorem e24KC2ThetaAboveLeaf0011221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112213)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112213)) h
theorem e24KC2ThetaAboveLeaf001122132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00112213) = true := by
  have h : ((childHL thetaAboveCell00112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00112213) h
theorem e24KC2ThetaAboveLeaf001122133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00112213) = true := by
  have h : ((childHH thetaAboveCell00112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00112213) h
theorem e24KC2ThetaAboveLeaf00112220 :
    adaptiveCoverCheck 11 thetaAboveCell00112220 = true := by
  have h : (thetaAboveCell00112220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112220 h
theorem e24KC2ThetaAboveLeaf00112221 :
    adaptiveCoverCheck 11 thetaAboveCell00112221 = true := by
  have h : (thetaAboveCell00112221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112221 h
theorem e24KC2ThetaAboveLeaf00112222 :
    adaptiveCoverCheck 11 thetaAboveCell00112222 = true := by
  have h : (thetaAboveCell00112222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112222 h
theorem e24KC2ThetaAboveLeaf00112223 :
    adaptiveCoverCheck 11 thetaAboveCell00112223 = true := by
  have h : (thetaAboveCell00112223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112223 h
theorem e24KC2ThetaAboveLeaf00112230 :
    adaptiveCoverCheck 11 thetaAboveCell00112230 = true := by
  have h : (thetaAboveCell00112230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112230 h
theorem e24KC2ThetaAboveLeaf00112231 :
    adaptiveCoverCheck 11 thetaAboveCell00112231 = true := by
  have h : (thetaAboveCell00112231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112231 h
theorem e24KC2ThetaAboveLeaf00112232 :
    adaptiveCoverCheck 11 thetaAboveCell00112232 = true := by
  have h : (thetaAboveCell00112232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112232 h
theorem e24KC2ThetaAboveLeaf00112233 :
    adaptiveCoverCheck 11 thetaAboveCell00112233 = true := by
  have h : (thetaAboveCell00112233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00112233 h
theorem e24KC2ThetaAboveLeaf001123000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00112300) = true := by
  have h : ((childLL thetaAboveCell00112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00112300) h
theorem e24KC2ThetaAboveLeaf001123001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00112300) = true := by
  have h : ((childLH thetaAboveCell00112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00112300) h
theorem e24KC2ThetaAboveLeaf001123010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00112301) = true := by
  have h : ((childLL thetaAboveCell00112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00112301) h
theorem e24KC2ThetaAboveLeaf001123011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00112301) = true := by
  have h : ((childLH thetaAboveCell00112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00112301) h
theorem e24KC2ThetaAboveLeaf0011230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112302)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112302)) h
theorem e24KC2ThetaAboveLeaf0011230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112302)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112302)) h
theorem e24KC2ThetaAboveLeaf0011230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112302)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112302)) h
theorem e24KC2ThetaAboveLeaf0011230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112302)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112302)) h
theorem e24KC2ThetaAboveLeaf001123022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00112302) = true := by
  have h : ((childHL thetaAboveCell00112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00112302) h
theorem e24KC2ThetaAboveLeaf001123023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00112302) = true := by
  have h : ((childHH thetaAboveCell00112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00112302) h
theorem e24KC2ThetaAboveLeaf0011230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112303)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112303)) h
theorem e24KC2ThetaAboveLeaf0011230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112303)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112303)) h
theorem e24KC2ThetaAboveLeaf0011230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112303)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112303)) h
theorem e24KC2ThetaAboveLeaf0011230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112303)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112303)) h
theorem e24KC2ThetaAboveLeaf001123032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00112303) = true := by
  have h : ((childHL thetaAboveCell00112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00112303) h
theorem e24KC2ThetaAboveLeaf001123033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00112303) = true := by
  have h : ((childHH thetaAboveCell00112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00112303) h
theorem e24KC2ThetaAboveLeaf001123100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00112310) = true := by
  have h : ((childLL thetaAboveCell00112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00112310) h
theorem e24KC2ThetaAboveLeaf001123101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00112310) = true := by
  have h : ((childLH thetaAboveCell00112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00112310) h
theorem e24KC2ThetaAboveLeaf001123110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00112311) = true := by
  have h : ((childLL thetaAboveCell00112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00112311) h
theorem e24KC2ThetaAboveLeaf001123111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00112311) = true := by
  have h : ((childLH thetaAboveCell00112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00112311) h
theorem e24KC2ThetaAboveLeaf0011231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00112311)) = true := by
  have h : ((childLH (childHL thetaAboveCell00112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell00112311)) h
theorem e24KC2ThetaAboveLeaf0011231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00112311)) = true := by
  have h : ((childLL (childHH thetaAboveCell00112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell00112311)) h
theorem e24KC2ThetaAboveLeaf0011231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00112311)) = true := by
  have h : ((childLH (childHH thetaAboveCell00112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell00112311)) h
theorem e24KC2ThetaAboveLeaf0011231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112312)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112312)) h
theorem e24KC2ThetaAboveLeaf0011231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112312)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112312)) h
theorem e24KC2ThetaAboveLeaf0011231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112312)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112312)) h
theorem e24KC2ThetaAboveLeaf0011231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112312)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112312)) h
theorem e24KC2ThetaAboveLeaf001123122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00112312) = true := by
  have h : ((childHL thetaAboveCell00112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00112312) h
theorem e24KC2ThetaAboveLeaf001123123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00112312) = true := by
  have h : ((childHH thetaAboveCell00112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00112312) h
theorem e24KC2ThetaAboveLeaf0011231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00112313)) = true := by
  have h : ((childHL (childLL thetaAboveCell00112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00112313)) h
theorem e24KC2ThetaAboveLeaf0011231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00112313)) = true := by
  have h : ((childHH (childLL thetaAboveCell00112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00112313)) h
theorem e24KC2ThetaAboveLeaf0011231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00112313)) = true := by
  have h : ((childHL (childLH thetaAboveCell00112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00112313)) h
theorem e24KC2ThetaAboveLeaf0011231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00112313)) = true := by
  have h : ((childHH (childLH thetaAboveCell00112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00112313)) h
theorem e24KC2ThetaAboveLeaf001123132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00112313) = true := by
  have h : ((childHL thetaAboveCell00112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00112313) h

end PartE
end GerverSofa

end

end

end
