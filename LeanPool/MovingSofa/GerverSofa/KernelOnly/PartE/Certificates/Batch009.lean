/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT307200009`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC5 checkpoint-aware kernel batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb518b98fbe

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `0111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24ThetaAboveRoot)))
/-- Subcell `01103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0110)))
/-- Subcell `01103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01103333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0110)))
/-- Subcell `01112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0111)))
/-- Subcell `01112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0111)))
/-- Subcell `01112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0111)))
/-- Subcell `01112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0111)))
/-- Subcell `01112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0111)))
/-- Subcell `01112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0111)))
/-- Subcell `01112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0111)))
/-- Subcell `01112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0111)))
/-- Subcell `01112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0111)))
/-- Subcell `01112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0111)))
/-- Subcell `01112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0111)))
/-- Subcell `01112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0111)))
/-- Subcell `01112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0111)))
/-- Subcell `01112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0111)))
/-- Subcell `01112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0111)))
/-- Subcell `01112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0111)))
/-- Subcell `01112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0111)))
/-- Subcell `01112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01112333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0111)))
/-- Subcell `01113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0111)))
/-- Subcell `01113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0111)))
/-- Subcell `01113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0111)))
/-- Subcell `01113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0111)))
/-- Subcell `01113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0111)))
/-- Subcell `01113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0111)))
/-- Subcell `01113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0111)))
/-- Subcell `01113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0111)))
/-- Subcell `01113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0111)))
/-- Subcell `01113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0111)))
/-- Subcell `01113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0111)))
/-- Subcell `01113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0111)))
/-- Subcell `01113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0111)))
/-- Subcell `01113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0111)))
/-- Subcell `01113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0111)))
/-- Subcell `01113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0111)))
/-- Subcell `01113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0111)))
/-- Subcell `01113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0111)))

end CertificateCellsb518b98fbe

open CertificateCellsb518b98fbe
theorem e24KC2ThetaAboveLeaf0110321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103210)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103210)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf011032110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103211) = true := by
  have h : ((childLL thetaAboveCell01103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103211) h
theorem e24KC2ThetaAboveLeaf011032111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103211) = true := by
  have h : ((childLH thetaAboveCell01103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103211) h
theorem e24KC2ThetaAboveLeaf0110321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103211)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103211)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103211)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103211)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf011032200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103220) = true := by
  have h : ((childLL thetaAboveCell01103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103220) h
theorem e24KC2ThetaAboveLeaf011032201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103220) = true := by
  have h : ((childLH thetaAboveCell01103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103220) h
theorem e24KC2ThetaAboveLeaf011032202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103220) = true := by
  have h : ((childHL thetaAboveCell01103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103220) h
theorem e24KC2ThetaAboveLeaf011032203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103220) = true := by
  have h : ((childHH thetaAboveCell01103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103220) h
theorem e24KC2ThetaAboveLeaf011032210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103221) = true := by
  have h : ((childLL thetaAboveCell01103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103221) h
theorem e24KC2ThetaAboveLeaf011032211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103221) = true := by
  have h : ((childLH thetaAboveCell01103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103221) h
theorem e24KC2ThetaAboveLeaf011032212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103221) = true := by
  have h : ((childHL thetaAboveCell01103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103221) h
theorem e24KC2ThetaAboveLeaf011032213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103221) = true := by
  have h : ((childHH thetaAboveCell01103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103221) h
theorem e24KC2ThetaAboveLeaf01103222 :
    adaptiveCoverCheck 11 thetaAboveCell01103222 = true := by
  have h : (thetaAboveCell01103222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103222 h
theorem e24KC2ThetaAboveLeaf01103223 :
    adaptiveCoverCheck 11 thetaAboveCell01103223 = true := by
  have h : (thetaAboveCell01103223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103223 h
theorem e24KC2ThetaAboveLeaf011032300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103230) = true := by
  have h : ((childLL thetaAboveCell01103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103230) h
theorem e24KC2ThetaAboveLeaf011032301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103230) = true := by
  have h : ((childLH thetaAboveCell01103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103230) h
theorem e24KC2ThetaAboveLeaf011032302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103230) = true := by
  have h : ((childHL thetaAboveCell01103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103230) h
theorem e24KC2ThetaAboveLeaf011032303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103230) = true := by
  have h : ((childHH thetaAboveCell01103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103230) h
theorem e24KC2ThetaAboveLeaf011032310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103231) = true := by
  have h : ((childLL thetaAboveCell01103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103231) h
theorem e24KC2ThetaAboveLeaf011032311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103231) = true := by
  have h : ((childLH thetaAboveCell01103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103231) h
theorem e24KC2ThetaAboveLeaf011032312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103231) = true := by
  have h : ((childHL thetaAboveCell01103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103231) h
theorem e24KC2ThetaAboveLeaf011032313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103231) = true := by
  have h : ((childHH thetaAboveCell01103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103231) h
theorem e24KC2ThetaAboveLeaf01103232 :
    adaptiveCoverCheck 11 thetaAboveCell01103232 = true := by
  have h : (thetaAboveCell01103232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103232 h
theorem e24KC2ThetaAboveLeaf01103233 :
    adaptiveCoverCheck 11 thetaAboveCell01103233 = true := by
  have h : (thetaAboveCell01103233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103233 h
theorem e24KC2ThetaAboveLeaf011033000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103300) = true := by
  have h : ((childLL thetaAboveCell01103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103300) h
theorem e24KC2ThetaAboveLeaf011033001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103300) = true := by
  have h : ((childLH thetaAboveCell01103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103300) h
theorem e24KC2ThetaAboveLeaf0110330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103300)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103300)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103300)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103300)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf011033010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103301) = true := by
  have h : ((childLL thetaAboveCell01103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103301) h
theorem e24KC2ThetaAboveLeaf011033011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103301) = true := by
  have h : ((childLH thetaAboveCell01103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103301) h
theorem e24KC2ThetaAboveLeaf0110330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103301)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103301)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103301)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103301)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf011033100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103310) = true := by
  have h : ((childLL thetaAboveCell01103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103310) h
theorem e24KC2ThetaAboveLeaf011033101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103310) = true := by
  have h : ((childLH thetaAboveCell01103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103310) h
theorem e24KC2ThetaAboveLeaf0110331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103310)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103310)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103310)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103310)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf011033110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103311) = true := by
  have h : ((childLL thetaAboveCell01103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103311) h
theorem e24KC2ThetaAboveLeaf011033111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103311) = true := by
  have h : ((childLH thetaAboveCell01103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103311) h
theorem e24KC2ThetaAboveLeaf0110331120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103311)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103311)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103311)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103311)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf011033200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103320) = true := by
  have h : ((childLL thetaAboveCell01103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103320) h
theorem e24KC2ThetaAboveLeaf011033201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103320) = true := by
  have h : ((childLH thetaAboveCell01103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103320) h
theorem e24KC2ThetaAboveLeaf011033202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103320) = true := by
  have h : ((childHL thetaAboveCell01103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103320) h
theorem e24KC2ThetaAboveLeaf011033203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103320) = true := by
  have h : ((childHH thetaAboveCell01103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103320) h
theorem e24KC2ThetaAboveLeaf011033210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103321) = true := by
  have h : ((childLL thetaAboveCell01103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103321) h
theorem e24KC2ThetaAboveLeaf011033211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103321) = true := by
  have h : ((childLH thetaAboveCell01103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103321) h
theorem e24KC2ThetaAboveLeaf011033212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103321) = true := by
  have h : ((childHL thetaAboveCell01103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103321) h
theorem e24KC2ThetaAboveLeaf011033213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103321) = true := by
  have h : ((childHH thetaAboveCell01103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103321) h
theorem e24KC2ThetaAboveLeaf01103322 :
    adaptiveCoverCheck 11 thetaAboveCell01103322 = true := by
  have h : (thetaAboveCell01103322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103322 h
theorem e24KC2ThetaAboveLeaf01103323 :
    adaptiveCoverCheck 11 thetaAboveCell01103323 = true := by
  have h : (thetaAboveCell01103323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103323 h
theorem e24KC2ThetaAboveLeaf011033300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103330) = true := by
  have h : ((childLL thetaAboveCell01103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103330) h
theorem e24KC2ThetaAboveLeaf011033301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103330) = true := by
  have h : ((childLH thetaAboveCell01103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103330) h
theorem e24KC2ThetaAboveLeaf011033302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103330) = true := by
  have h : ((childHL thetaAboveCell01103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103330) h
theorem e24KC2ThetaAboveLeaf011033303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103330) = true := by
  have h : ((childHH thetaAboveCell01103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103330) h
theorem e24KC2ThetaAboveLeaf011033310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103331) = true := by
  have h : ((childLL thetaAboveCell01103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103331) h
theorem e24KC2ThetaAboveLeaf011033311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103331) = true := by
  have h : ((childLH thetaAboveCell01103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103331) h
theorem e24KC2ThetaAboveLeaf011033312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103331) = true := by
  have h : ((childHL thetaAboveCell01103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103331) h
theorem e24KC2ThetaAboveLeaf011033313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103331) = true := by
  have h : ((childHH thetaAboveCell01103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103331) h
theorem e24KC2ThetaAboveLeaf01103332 :
    adaptiveCoverCheck 11 thetaAboveCell01103332 = true := by
  have h : (thetaAboveCell01103332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103332 h
theorem e24KC2ThetaAboveLeaf01103333 :
    adaptiveCoverCheck 11 thetaAboveCell01103333 = true := by
  have h : (thetaAboveCell01103333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103333 h
theorem e24KC2ThetaAboveLeaf011100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0111)) = true := by
  have h : ((childLL (childLL thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0111)) = true := by
  have h : ((childLH (childLL thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0111)) = true := by
  have h : ((childHL (childLL thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0111)) = true := by
  have h : ((childHH (childLL thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0111)) = true := by
  have h : ((childLL (childLH thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0111)) = true := by
  have h : ((childLH (childLH thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0111)) = true := by
  have h : ((childHL (childLH thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0111)) = true := by
  have h : ((childHH (childLH thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf0111200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0111))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf0111201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0111))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf01112020 :
    adaptiveCoverCheck 11 thetaAboveCell01112020 = true := by
  have h : (thetaAboveCell01112020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112020 h
theorem e24KC2ThetaAboveLeaf01112021 :
    adaptiveCoverCheck 11 thetaAboveCell01112021 = true := by
  have h : (thetaAboveCell01112021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112021 h
theorem e24KC2ThetaAboveLeaf01112022 :
    adaptiveCoverCheck 11 thetaAboveCell01112022 = true := by
  have h : (thetaAboveCell01112022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112022 h
theorem e24KC2ThetaAboveLeaf01112023 :
    adaptiveCoverCheck 11 thetaAboveCell01112023 = true := by
  have h : (thetaAboveCell01112023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112023 h
theorem e24KC2ThetaAboveLeaf01112030 :
    adaptiveCoverCheck 11 thetaAboveCell01112030 = true := by
  have h : (thetaAboveCell01112030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112030 h
theorem e24KC2ThetaAboveLeaf01112031 :
    adaptiveCoverCheck 11 thetaAboveCell01112031 = true := by
  have h : (thetaAboveCell01112031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112031 h
theorem e24KC2ThetaAboveLeaf01112032 :
    adaptiveCoverCheck 11 thetaAboveCell01112032 = true := by
  have h : (thetaAboveCell01112032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112032 h
theorem e24KC2ThetaAboveLeaf01112033 :
    adaptiveCoverCheck 11 thetaAboveCell01112033 = true := by
  have h : (thetaAboveCell01112033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112033 h
theorem e24KC2ThetaAboveLeaf0111210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0111))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf0111211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0111))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf01112120 :
    adaptiveCoverCheck 11 thetaAboveCell01112120 = true := by
  have h : (thetaAboveCell01112120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112120 h
theorem e24KC2ThetaAboveLeaf01112121 :
    adaptiveCoverCheck 11 thetaAboveCell01112121 = true := by
  have h : (thetaAboveCell01112121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112121 h
theorem e24KC2ThetaAboveLeaf01112122 :
    adaptiveCoverCheck 11 thetaAboveCell01112122 = true := by
  have h : (thetaAboveCell01112122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112122 h
theorem e24KC2ThetaAboveLeaf01112123 :
    adaptiveCoverCheck 11 thetaAboveCell01112123 = true := by
  have h : (thetaAboveCell01112123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112123 h
theorem e24KC2ThetaAboveLeaf01112130 :
    adaptiveCoverCheck 11 thetaAboveCell01112130 = true := by
  have h : (thetaAboveCell01112130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112130 h
theorem e24KC2ThetaAboveLeaf01112131 :
    adaptiveCoverCheck 11 thetaAboveCell01112131 = true := by
  have h : (thetaAboveCell01112131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112131 h
theorem e24KC2ThetaAboveLeaf01112132 :
    adaptiveCoverCheck 11 thetaAboveCell01112132 = true := by
  have h : (thetaAboveCell01112132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112132 h
theorem e24KC2ThetaAboveLeaf01112133 :
    adaptiveCoverCheck 11 thetaAboveCell01112133 = true := by
  have h : (thetaAboveCell01112133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112133 h
theorem e24KC2ThetaAboveLeaf011122000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112200) = true := by
  have h : ((childLL thetaAboveCell01112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112200) h
theorem e24KC2ThetaAboveLeaf011122001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112200) = true := by
  have h : ((childLH thetaAboveCell01112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112200) h
theorem e24KC2ThetaAboveLeaf0111220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112200)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112200)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112200)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112200)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf011122010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112201) = true := by
  have h : ((childLL thetaAboveCell01112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112201) h
theorem e24KC2ThetaAboveLeaf011122011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112201) = true := by
  have h : ((childLH thetaAboveCell01112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112201) h
theorem e24KC2ThetaAboveLeaf0111220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112201)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112201)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112201)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112201)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf011122100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112210) = true := by
  have h : ((childLL thetaAboveCell01112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112210) h
theorem e24KC2ThetaAboveLeaf011122101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112210) = true := by
  have h : ((childLH thetaAboveCell01112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112210) h
theorem e24KC2ThetaAboveLeaf0111221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112210)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112210)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112210)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112210)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112210)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112210)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf011122110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112211) = true := by
  have h : ((childLL thetaAboveCell01112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112211) h
theorem e24KC2ThetaAboveLeaf011122111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112211) = true := by
  have h : ((childLH thetaAboveCell01112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112211) h
theorem e24KC2ThetaAboveLeaf0111221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112211)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112211)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112211)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112211)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf011122200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112220) = true := by
  have h : ((childLL thetaAboveCell01112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112220) h
theorem e24KC2ThetaAboveLeaf011122201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112220) = true := by
  have h : ((childLH thetaAboveCell01112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112220) h
theorem e24KC2ThetaAboveLeaf011122202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112220) = true := by
  have h : ((childHL thetaAboveCell01112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112220) h
theorem e24KC2ThetaAboveLeaf011122203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112220) = true := by
  have h : ((childHH thetaAboveCell01112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112220) h
theorem e24KC2ThetaAboveLeaf011122210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112221) = true := by
  have h : ((childLL thetaAboveCell01112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112221) h
theorem e24KC2ThetaAboveLeaf011122211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112221) = true := by
  have h : ((childLH thetaAboveCell01112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112221) h
theorem e24KC2ThetaAboveLeaf011122212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112221) = true := by
  have h : ((childHL thetaAboveCell01112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112221) h
theorem e24KC2ThetaAboveLeaf011122213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112221) = true := by
  have h : ((childHH thetaAboveCell01112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112221) h
theorem e24KC2ThetaAboveLeaf01112222 :
    adaptiveCoverCheck 11 thetaAboveCell01112222 = true := by
  have h : (thetaAboveCell01112222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112222 h
theorem e24KC2ThetaAboveLeaf01112223 :
    adaptiveCoverCheck 11 thetaAboveCell01112223 = true := by
  have h : (thetaAboveCell01112223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112223 h
theorem e24KC2ThetaAboveLeaf011122300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112230) = true := by
  have h : ((childLL thetaAboveCell01112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112230) h
theorem e24KC2ThetaAboveLeaf011122301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112230) = true := by
  have h : ((childLH thetaAboveCell01112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112230) h
theorem e24KC2ThetaAboveLeaf011122302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112230) = true := by
  have h : ((childHL thetaAboveCell01112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112230) h
theorem e24KC2ThetaAboveLeaf011122303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112230) = true := by
  have h : ((childHH thetaAboveCell01112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112230) h
theorem e24KC2ThetaAboveLeaf011122310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112231) = true := by
  have h : ((childLL thetaAboveCell01112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112231) h
theorem e24KC2ThetaAboveLeaf011122311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112231) = true := by
  have h : ((childLH thetaAboveCell01112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112231) h
theorem e24KC2ThetaAboveLeaf011122312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112231) = true := by
  have h : ((childHL thetaAboveCell01112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112231) h
theorem e24KC2ThetaAboveLeaf011122313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112231) = true := by
  have h : ((childHH thetaAboveCell01112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112231) h
theorem e24KC2ThetaAboveLeaf01112232 :
    adaptiveCoverCheck 11 thetaAboveCell01112232 = true := by
  have h : (thetaAboveCell01112232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112232 h
theorem e24KC2ThetaAboveLeaf01112233 :
    adaptiveCoverCheck 11 thetaAboveCell01112233 = true := by
  have h : (thetaAboveCell01112233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112233 h
theorem e24KC2ThetaAboveLeaf011123000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112300) = true := by
  have h : ((childLL thetaAboveCell01112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112300) h
theorem e24KC2ThetaAboveLeaf011123001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112300) = true := by
  have h : ((childLH thetaAboveCell01112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112300) h
theorem e24KC2ThetaAboveLeaf0111230020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112300)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112300)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112300)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112300)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf011123010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112301) = true := by
  have h : ((childLL thetaAboveCell01112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112301) h
theorem e24KC2ThetaAboveLeaf011123011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112301) = true := by
  have h : ((childLH thetaAboveCell01112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112301) h
theorem e24KC2ThetaAboveLeaf0111230120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112301)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112301)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112301)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112301)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf011123100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112310) = true := by
  have h : ((childLL thetaAboveCell01112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112310) h
theorem e24KC2ThetaAboveLeaf011123101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112310) = true := by
  have h : ((childLH thetaAboveCell01112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112310) h
theorem e24KC2ThetaAboveLeaf0111231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112310)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112310)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112310)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112310)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf011123110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112311) = true := by
  have h : ((childLL thetaAboveCell01112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112311) h
theorem e24KC2ThetaAboveLeaf011123111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112311) = true := by
  have h : ((childLH thetaAboveCell01112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112311) h
theorem e24KC2ThetaAboveLeaf0111231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112311)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112311)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112311)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112311)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf011123200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112320) = true := by
  have h : ((childLL thetaAboveCell01112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112320) h
theorem e24KC2ThetaAboveLeaf011123201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112320) = true := by
  have h : ((childLH thetaAboveCell01112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112320) h
theorem e24KC2ThetaAboveLeaf011123202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112320) = true := by
  have h : ((childHL thetaAboveCell01112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112320) h
theorem e24KC2ThetaAboveLeaf011123203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112320) = true := by
  have h : ((childHH thetaAboveCell01112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112320) h
theorem e24KC2ThetaAboveLeaf011123210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112321) = true := by
  have h : ((childLL thetaAboveCell01112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112321) h
theorem e24KC2ThetaAboveLeaf011123211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112321) = true := by
  have h : ((childLH thetaAboveCell01112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112321) h
theorem e24KC2ThetaAboveLeaf011123212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112321) = true := by
  have h : ((childHL thetaAboveCell01112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112321) h
theorem e24KC2ThetaAboveLeaf011123213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112321) = true := by
  have h : ((childHH thetaAboveCell01112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112321) h
theorem e24KC2ThetaAboveLeaf01112322 :
    adaptiveCoverCheck 11 thetaAboveCell01112322 = true := by
  have h : (thetaAboveCell01112322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112322 h
theorem e24KC2ThetaAboveLeaf01112323 :
    adaptiveCoverCheck 11 thetaAboveCell01112323 = true := by
  have h : (thetaAboveCell01112323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112323 h
theorem e24KC2ThetaAboveLeaf011123300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112330) = true := by
  have h : ((childLL thetaAboveCell01112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112330) h
theorem e24KC2ThetaAboveLeaf011123301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112330) = true := by
  have h : ((childLH thetaAboveCell01112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112330) h
theorem e24KC2ThetaAboveLeaf011123302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112330) = true := by
  have h : ((childHL thetaAboveCell01112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112330) h
theorem e24KC2ThetaAboveLeaf011123303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112330) = true := by
  have h : ((childHH thetaAboveCell01112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112330) h
theorem e24KC2ThetaAboveLeaf011123310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112331) = true := by
  have h : ((childLL thetaAboveCell01112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112331) h
theorem e24KC2ThetaAboveLeaf011123311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112331) = true := by
  have h : ((childLH thetaAboveCell01112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112331) h
theorem e24KC2ThetaAboveLeaf011123312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112331) = true := by
  have h : ((childHL thetaAboveCell01112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112331) h
theorem e24KC2ThetaAboveLeaf011123313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112331) = true := by
  have h : ((childHH thetaAboveCell01112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112331) h
theorem e24KC2ThetaAboveLeaf01112332 :
    adaptiveCoverCheck 11 thetaAboveCell01112332 = true := by
  have h : (thetaAboveCell01112332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112332 h
theorem e24KC2ThetaAboveLeaf01112333 :
    adaptiveCoverCheck 11 thetaAboveCell01112333 = true := by
  have h : (thetaAboveCell01112333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112333 h
theorem e24KC2ThetaAboveLeaf0111300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0111))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf0111301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0111))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf01113020 :
    adaptiveCoverCheck 11 thetaAboveCell01113020 = true := by
  have h : (thetaAboveCell01113020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113020 h
theorem e24KC2ThetaAboveLeaf01113021 :
    adaptiveCoverCheck 11 thetaAboveCell01113021 = true := by
  have h : (thetaAboveCell01113021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113021 h
theorem e24KC2ThetaAboveLeaf01113022 :
    adaptiveCoverCheck 11 thetaAboveCell01113022 = true := by
  have h : (thetaAboveCell01113022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113022 h
theorem e24KC2ThetaAboveLeaf01113023 :
    adaptiveCoverCheck 11 thetaAboveCell01113023 = true := by
  have h : (thetaAboveCell01113023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113023 h
theorem e24KC2ThetaAboveLeaf01113030 :
    adaptiveCoverCheck 11 thetaAboveCell01113030 = true := by
  have h : (thetaAboveCell01113030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113030 h
theorem e24KC2ThetaAboveLeaf01113031 :
    adaptiveCoverCheck 11 thetaAboveCell01113031 = true := by
  have h : (thetaAboveCell01113031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113031 h
theorem e24KC2ThetaAboveLeaf01113032 :
    adaptiveCoverCheck 11 thetaAboveCell01113032 = true := by
  have h : (thetaAboveCell01113032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113032 h
theorem e24KC2ThetaAboveLeaf01113033 :
    adaptiveCoverCheck 11 thetaAboveCell01113033 = true := by
  have h : (thetaAboveCell01113033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113033 h
theorem e24KC2ThetaAboveLeaf0111310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0111))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf0111311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0111))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf01113120 :
    adaptiveCoverCheck 11 thetaAboveCell01113120 = true := by
  have h : (thetaAboveCell01113120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113120 h
theorem e24KC2ThetaAboveLeaf01113121 :
    adaptiveCoverCheck 11 thetaAboveCell01113121 = true := by
  have h : (thetaAboveCell01113121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113121 h
theorem e24KC2ThetaAboveLeaf01113122 :
    adaptiveCoverCheck 11 thetaAboveCell01113122 = true := by
  have h : (thetaAboveCell01113122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113122 h
theorem e24KC2ThetaAboveLeaf01113123 :
    adaptiveCoverCheck 11 thetaAboveCell01113123 = true := by
  have h : (thetaAboveCell01113123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113123 h
theorem e24KC2ThetaAboveLeaf01113130 :
    adaptiveCoverCheck 11 thetaAboveCell01113130 = true := by
  have h : (thetaAboveCell01113130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113130 h
theorem e24KC2ThetaAboveLeaf01113131 :
    adaptiveCoverCheck 11 thetaAboveCell01113131 = true := by
  have h : (thetaAboveCell01113131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113131 h
theorem e24KC2ThetaAboveLeaf01113132 :
    adaptiveCoverCheck 11 thetaAboveCell01113132 = true := by
  have h : (thetaAboveCell01113132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113132 h
theorem e24KC2ThetaAboveLeaf01113133 :
    adaptiveCoverCheck 11 thetaAboveCell01113133 = true := by
  have h : (thetaAboveCell01113133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113133 h
theorem e24KC2ThetaAboveLeaf011132000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113200) = true := by
  have h : ((childLL thetaAboveCell01113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113200) h
theorem e24KC2ThetaAboveLeaf011132001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113200) = true := by
  have h : ((childLH thetaAboveCell01113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113200) h
theorem e24KC2ThetaAboveLeaf0111320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113200)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113200)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113200)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113200)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf011132010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113201) = true := by
  have h : ((childLL thetaAboveCell01113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113201) h
theorem e24KC2ThetaAboveLeaf011132011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113201) = true := by
  have h : ((childLH thetaAboveCell01113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113201) h
theorem e24KC2ThetaAboveLeaf0111320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113201)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113201)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113201)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113201)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113202)) h

end PartE
end GerverSofa

end

end

end
