/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatch11b2bedf1dcd3516`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC6 explicit proof-producing certificate batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2d2385ed48

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0000)))
/-- Subcell `00002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0000)))
/-- Subcell `00002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0000)))
/-- Subcell `000022103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002210)))
/-- Subcell `000022110220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00002211)))
/-- Subcell `000022110221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00002211)))
/-- Subcell `000022110222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00002211)))
/-- Subcell `000022110223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00002211)))
/-- Subcell `000022110230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00002211)))
/-- Subcell `000022110231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00002211)))
/-- Subcell `000022110232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00002211)))
/-- Subcell `000022110233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00002211)))
/-- Subcell `000022110320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00002211)))
/-- Subcell `000022110321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00002211)))
/-- Subcell `000022110322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00002211)))
/-- Subcell `000022110323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00002211)))
/-- Subcell `000022110330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00002211)))
/-- Subcell `000022110331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00002211)))
/-- Subcell `000022110332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00002211)))
/-- Subcell `000022110333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00002211)))
/-- Subcell `000022111220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00002211)))
/-- Subcell `000022111221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00002211)))
/-- Subcell `000022111222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00002211)))
/-- Subcell `000022111223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00002211)))
/-- Subcell `000022111230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaAboveCell00002211)))
/-- Subcell `000022111231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaAboveCell00002211)))
/-- Subcell `000022111232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaAboveCell00002211)))
/-- Subcell `000022111233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaAboveCell00002211)))
/-- Subcell `000022111320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaAboveCell00002211)))
/-- Subcell `000022111321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaAboveCell00002211)))
/-- Subcell `000022111322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaAboveCell00002211)))
/-- Subcell `000022111323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaAboveCell00002211)))
/-- Subcell `000022111330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaAboveCell00002211)))
/-- Subcell `000022111331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaAboveCell00002211)))
/-- Subcell `000022111332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaAboveCell00002211)))
/-- Subcell `000022111333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaAboveCell00002211)))
/-- Subcell `000022112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002211)))
/-- Subcell `000022112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002211)))
/-- Subcell `000022113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002211)))
/-- Subcell `000022113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000022113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002211)))
/-- Subcell `000023000220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00002300)))
/-- Subcell `000023000221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00002300)))
/-- Subcell `000023000222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00002300)))
/-- Subcell `000023000223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00002300)))
/-- Subcell `000023000230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00002300)))
/-- Subcell `000023000231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00002300)))
/-- Subcell `000023000232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00002300)))
/-- Subcell `000023000233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00002300)))
/-- Subcell `000023000320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00002300)))
/-- Subcell `000023000321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00002300)))
/-- Subcell `000023000322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00002300)))
/-- Subcell `000023000323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00002300)))
/-- Subcell `000023000330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00002300)))
/-- Subcell `000023000331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00002300)))
/-- Subcell `000023000332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00002300)))
/-- Subcell `000023000333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00002300)))
/-- Subcell `000023001220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00002300)))
/-- Subcell `000023001221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00002300)))
/-- Subcell `000023001222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00002300)))
/-- Subcell `000023001223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00002300)))
/-- Subcell `000023001230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaAboveCell00002300)))
/-- Subcell `000023001231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaAboveCell00002300)))
/-- Subcell `000023001232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaAboveCell00002300)))
/-- Subcell `000023001233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaAboveCell00002300)))
/-- Subcell `000023001320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaAboveCell00002300)))
/-- Subcell `000023001321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaAboveCell00002300)))
/-- Subcell `000023001322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaAboveCell00002300)))
/-- Subcell `000023001323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaAboveCell00002300)))
/-- Subcell `000023001330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaAboveCell00002300)))
/-- Subcell `000023001331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaAboveCell00002300)))
/-- Subcell `000023001332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaAboveCell00002300)))
/-- Subcell `000023001333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaAboveCell00002300)))

end CertificateCells2d2385ed48

open CertificateCells2d2385ed48
theorem cover_subtree_edb64f01a0c6 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103100)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022103100))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022103100))) h))
    (by
      have h : ((childLH (childHL thetaAboveCell000022103100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022103100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103100))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103100))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103100))) h))

theorem cover_subtree_a40a1df9b3a1 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103100)
    (by
      have h : ((childLL (childHH thetaAboveCell000022103100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022103100)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022103100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022103100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103100))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103100))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103100))) h))

theorem cover_subtree_e870c75d402b :
    adaptiveCoverCheck 7 thetaAboveCell000022103100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103100
    (by
      have h : ((childLL thetaAboveCell000022103100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103100) h)
    (by
      have h : ((childLH thetaAboveCell000022103100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103100) h)
    cover_subtree_edb64f01a0c6
    cover_subtree_a40a1df9b3a1

theorem cover_subtree_5efea1d56268 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103101)
    (by
      have h : ((childLL (childHL thetaAboveCell000022103101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022103101)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022103101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022103101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103101))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103101))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103101))) h))

theorem cover_subtree_d2aa99fffe31 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103101)
    (by
      have h : ((childLL (childHH thetaAboveCell000022103101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022103101)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022103101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022103101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103101))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103101))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103101))) h))

theorem cover_subtree_0abbf33fdebf :
    adaptiveCoverCheck 7 thetaAboveCell000022103101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103101
    (by
      have h : ((childLL thetaAboveCell000022103101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103101) h)
    (by
      have h : ((childLH thetaAboveCell000022103101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103101) h)
    cover_subtree_5efea1d56268
    cover_subtree_d2aa99fffe31

theorem cover_subtree_1d0945e98034 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103102))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103102))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103102))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103102)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103102)) h)

theorem cover_subtree_e19e97fa44f4 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103102))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103102))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103102))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103102)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103102)) h)

theorem cover_subtree_92cf9ed4da50 :
    adaptiveCoverCheck 7 thetaAboveCell000022103102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103102
    cover_subtree_1d0945e98034
    cover_subtree_e19e97fa44f4
    (by
      have h : ((childHL thetaAboveCell000022103102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103102) h)
    (by
      have h : ((childHH thetaAboveCell000022103102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103102) h)

theorem cover_subtree_637f019f84f2 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103103))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103103))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103103))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103103)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103103)) h)

theorem cover_subtree_2f9a3a39c9a5 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103103))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103103))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103103))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103103)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103103)) h)

theorem cover_subtree_30350e948f84 :
    adaptiveCoverCheck 7 thetaAboveCell000022103103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103103
    cover_subtree_637f019f84f2
    cover_subtree_2f9a3a39c9a5
    (by
      have h : ((childHL thetaAboveCell000022103103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103103) h)
    (by
      have h : ((childHH thetaAboveCell000022103103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103103) h)

theorem cover_subtree_4a228fe99e26 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002210)))
    cover_subtree_e870c75d402b
    cover_subtree_0abbf33fdebf
    cover_subtree_92cf9ed4da50
    cover_subtree_30350e948f84

theorem cover_subtree_dec56845b136 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103110)
    (by
      have h : ((childLL (childHL thetaAboveCell000022103110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022103110)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022103110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022103110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103110))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103110))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103110))) h))

theorem cover_subtree_6de59f8bb098 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103110)
    (by
      have h : ((childLL (childHH thetaAboveCell000022103110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022103110)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022103110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022103110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103110))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103110))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103110))) h))

theorem cover_subtree_ab36c8726f5a :
    adaptiveCoverCheck 7 thetaAboveCell000022103110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103110
    (by
      have h : ((childLL thetaAboveCell000022103110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103110) h)
    (by
      have h : ((childLH thetaAboveCell000022103110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103110) h)
    cover_subtree_dec56845b136
    cover_subtree_6de59f8bb098

theorem cover_subtree_59e28493c6fc :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103111)
    (by
      have h : ((childLL (childHL thetaAboveCell000022103111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022103111)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022103111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022103111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103111))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103111))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103111))) h))

theorem cover_subtree_de44712e43a7 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103111)
    (by
      have h : ((childLL (childHH thetaAboveCell000022103111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022103111)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022103111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022103111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103111))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103111))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103111))) h))

theorem cover_subtree_526ec4bd5c8b :
    adaptiveCoverCheck 7 thetaAboveCell000022103111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103111
    (by
      have h : ((childLL thetaAboveCell000022103111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103111) h)
    (by
      have h : ((childLH thetaAboveCell000022103111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103111) h)
    cover_subtree_59e28493c6fc
    cover_subtree_de44712e43a7

theorem cover_subtree_f14f28c14e3c :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103112))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103112))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103112))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103112)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103112)) h)

theorem cover_subtree_2e18124844df :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103112))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103112))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103112))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103112)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103112)) h)

theorem cover_subtree_f0199f1a57d7 :
    adaptiveCoverCheck 7 thetaAboveCell000022103112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103112
    cover_subtree_f14f28c14e3c
    cover_subtree_2e18124844df
    (by
      have h : ((childHL thetaAboveCell000022103112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103112) h)
    (by
      have h : ((childHH thetaAboveCell000022103112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103112) h)

theorem cover_subtree_48a3af012806 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103113))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103113))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103113))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103113)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103113)) h)

theorem cover_subtree_e9c96ebadfa8 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103113))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103113))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103113))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103113)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103113)) h)

theorem cover_subtree_88cc51539fac :
    adaptiveCoverCheck 7 thetaAboveCell000022103113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103113
    cover_subtree_48a3af012806
    cover_subtree_e9c96ebadfa8
    (by
      have h : ((childHL thetaAboveCell000022103113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103113) h)
    (by
      have h : ((childHH thetaAboveCell000022103113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103113) h)

theorem cover_subtree_a1d8aa321d27 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002210)))
    cover_subtree_ab36c8726f5a
    cover_subtree_526ec4bd5c8b
    cover_subtree_f0199f1a57d7
    cover_subtree_88cc51539fac

theorem e24KC2ThetaAboveLeaf0000221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002210))
    cover_subtree_4a228fe99e26
    cover_subtree_a1d8aa321d27
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103120 h)
        (by
          have h : (thetaAboveCell000022103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103121 h)
        (by
          have h : (thetaAboveCell000022103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103122 h)
        (by
          have h : (thetaAboveCell000022103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103130 h)
        (by
          have h : (thetaAboveCell000022103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103131 h)
        (by
          have h : (thetaAboveCell000022103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103132 h)
        (by
          have h : (thetaAboveCell000022103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103133 h))
theorem e24KC2ThetaAboveLeaf0000221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002210))) h)
theorem e24KC2ThetaAboveLeaf0000221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002210))) h)
theorem e24KC2ThetaAboveLeaf0000221102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00002211))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00002211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022110220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110220 h)
        (by
          have h : (thetaAboveCell000022110221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110221 h)
        (by
          have h : (thetaAboveCell000022110222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110222 h)
        (by
          have h : (thetaAboveCell000022110223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022110230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110230 h)
        (by
          have h : (thetaAboveCell000022110231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110231 h)
        (by
          have h : (thetaAboveCell000022110232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110232 h)
        (by
          have h : (thetaAboveCell000022110233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110233 h))
theorem e24KC2ThetaAboveLeaf0000221103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00002211))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00002211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022110320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110320 h)
        (by
          have h : (thetaAboveCell000022110321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110321 h)
        (by
          have h : (thetaAboveCell000022110322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110322 h)
        (by
          have h : (thetaAboveCell000022110323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022110330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110330 h)
        (by
          have h : (thetaAboveCell000022110331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110331 h)
        (by
          have h : (thetaAboveCell000022110332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110332 h)
        (by
          have h : (thetaAboveCell000022110333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110333 h))
theorem e24KC2ThetaAboveLeaf0000221112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00002211))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00002211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022111220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111220 h)
        (by
          have h : (thetaAboveCell000022111221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111221 h)
        (by
          have h : (thetaAboveCell000022111222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111222 h)
        (by
          have h : (thetaAboveCell000022111223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022111230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111230 h)
        (by
          have h : (thetaAboveCell000022111231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111231 h)
        (by
          have h : (thetaAboveCell000022111232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111232 h)
        (by
          have h : (thetaAboveCell000022111233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111233 h))
theorem e24KC2ThetaAboveLeaf0000221113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00002211))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00002211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022111320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111320 h)
        (by
          have h : (thetaAboveCell000022111321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111321 h)
        (by
          have h : (thetaAboveCell000022111322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111322 h)
        (by
          have h : (thetaAboveCell000022111323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022111330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111330 h)
        (by
          have h : (thetaAboveCell000022111331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111331 h)
        (by
          have h : (thetaAboveCell000022111332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111332 h)
        (by
          have h : (thetaAboveCell000022111333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111333 h))
theorem cover_subtree_43fd6107c581 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112000)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112000)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112000))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112000))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112000))) h))

theorem cover_subtree_2f5d0def195d :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112000)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112000)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112000))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112000))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112000))) h))

theorem cover_subtree_b847b0feac2d :
    adaptiveCoverCheck 7 thetaAboveCell000022112000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112000
    (by
      have h : ((childLL thetaAboveCell000022112000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112000) h)
    (by
      have h : ((childLH thetaAboveCell000022112000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112000) h)
    cover_subtree_43fd6107c581
    cover_subtree_2f5d0def195d

theorem cover_subtree_4950fac9bab9 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112001)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112001)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112001))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112001))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112001))) h))

theorem cover_subtree_0e72524614ed :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112001)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112001)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112001))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112001))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112001))) h))

theorem cover_subtree_b10e2b341d50 :
    adaptiveCoverCheck 7 thetaAboveCell000022112001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112001
    (by
      have h : ((childLL thetaAboveCell000022112001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112001) h)
    (by
      have h : ((childLH thetaAboveCell000022112001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112001) h)
    cover_subtree_4950fac9bab9
    cover_subtree_0e72524614ed

theorem cover_subtree_76b490d87a4e :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112002))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112002))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112002))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112002)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112002)) h)

theorem cover_subtree_4b9c90d07695 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112002))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112002))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112002))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112002)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022112002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022112002)) h)

theorem cover_subtree_b7dd7162f0b9 :
    adaptiveCoverCheck 7 thetaAboveCell000022112002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112002
    cover_subtree_76b490d87a4e
    cover_subtree_4b9c90d07695
    (by
      have h : ((childHL thetaAboveCell000022112002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112002) h)
    (by
      have h : ((childHH thetaAboveCell000022112002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112002) h)

theorem cover_subtree_de29b5c5a11d :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112003))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112003))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112003))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112003)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112003)) h)

theorem cover_subtree_31f4d5809705 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112003))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112003))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112003))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112003)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022112003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022112003)) h)

theorem cover_subtree_c9c566e964a9 :
    adaptiveCoverCheck 7 thetaAboveCell000022112003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112003
    cover_subtree_de29b5c5a11d
    cover_subtree_31f4d5809705
    (by
      have h : ((childHL thetaAboveCell000022112003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112003) h)
    (by
      have h : ((childHH thetaAboveCell000022112003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112003) h)

theorem cover_subtree_da67754fe633 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002211)))
    cover_subtree_b847b0feac2d
    cover_subtree_b10e2b341d50
    cover_subtree_b7dd7162f0b9
    cover_subtree_c9c566e964a9

theorem cover_subtree_95f6e6d97c24 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112010)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112010)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112010))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112010))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112010))) h))

theorem cover_subtree_9c844972ea1f :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112010)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112010)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112010))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112010))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112010))) h))

theorem cover_subtree_04ff1f51c7c8 :
    adaptiveCoverCheck 7 thetaAboveCell000022112010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112010
    (by
      have h : ((childLL thetaAboveCell000022112010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112010) h)
    (by
      have h : ((childLH thetaAboveCell000022112010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112010) h)
    cover_subtree_95f6e6d97c24
    cover_subtree_9c844972ea1f

theorem cover_subtree_754b681a3e26 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112011)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112011)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112011))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112011))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112011))) h))

theorem cover_subtree_497a7c55810a :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112011)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112011)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112011))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112011))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112011))) h))

theorem cover_subtree_92922a2edd2b :
    adaptiveCoverCheck 7 thetaAboveCell000022112011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112011
    (by
      have h : ((childLL thetaAboveCell000022112011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112011) h)
    (by
      have h : ((childLH thetaAboveCell000022112011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112011) h)
    cover_subtree_754b681a3e26
    cover_subtree_497a7c55810a

theorem cover_subtree_bfdd630a1f02 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112012))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112012))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112012))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112012)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112012)) h)

theorem cover_subtree_d41a2b9225dd :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112012))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112012))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112012))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112012)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022112012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022112012)) h)

theorem cover_subtree_b54fc51b3ec8 :
    adaptiveCoverCheck 7 thetaAboveCell000022112012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112012
    cover_subtree_bfdd630a1f02
    cover_subtree_d41a2b9225dd
    (by
      have h : ((childHL thetaAboveCell000022112012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112012) h)
    (by
      have h : ((childHH thetaAboveCell000022112012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112012) h)

theorem cover_subtree_1ae8b8609603 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112013))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112013))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112013))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112013)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112013)) h)

theorem cover_subtree_254e7d6a1a8d :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112013))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112013))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112013))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112013)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022112013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022112013)) h)

theorem cover_subtree_316108a366aa :
    adaptiveCoverCheck 7 thetaAboveCell000022112013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112013
    cover_subtree_1ae8b8609603
    cover_subtree_254e7d6a1a8d
    (by
      have h : ((childHL thetaAboveCell000022112013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112013) h)
    (by
      have h : ((childHH thetaAboveCell000022112013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112013) h)

theorem cover_subtree_23a35d53c9e2 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00002211)))
    cover_subtree_04ff1f51c7c8
    cover_subtree_92922a2edd2b
    cover_subtree_b54fc51b3ec8
    cover_subtree_316108a366aa

theorem e24KC2ThetaAboveLeaf0000221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002211))
    cover_subtree_da67754fe633
    cover_subtree_23a35d53c9e2
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112020 h)
        (by
          have h : (thetaAboveCell000022112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112021 h)
        (by
          have h : (thetaAboveCell000022112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112022 h)
        (by
          have h : (thetaAboveCell000022112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112030 h)
        (by
          have h : (thetaAboveCell000022112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112031 h)
        (by
          have h : (thetaAboveCell000022112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112032 h)
        (by
          have h : (thetaAboveCell000022112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112033 h))
theorem cover_subtree_021e44d85b50 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112100)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112100)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112100))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112100))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112100))) h))

theorem cover_subtree_62fa6c2e1429 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112100)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112100)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112100))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112100))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112100))) h))

theorem cover_subtree_ff28352fdcbd :
    adaptiveCoverCheck 7 thetaAboveCell000022112100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112100
    (by
      have h : ((childLL thetaAboveCell000022112100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112100) h)
    (by
      have h : ((childLH thetaAboveCell000022112100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112100) h)
    cover_subtree_021e44d85b50
    cover_subtree_62fa6c2e1429

theorem cover_subtree_4284ed2ee8d6 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112101)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112101)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112101))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112101))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112101))) h))

theorem cover_subtree_21c449726701 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112101)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112101)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112101))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112101))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112101))) h))

theorem cover_subtree_ecd8fe40a0e6 :
    adaptiveCoverCheck 7 thetaAboveCell000022112101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112101
    (by
      have h : ((childLL thetaAboveCell000022112101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112101) h)
    (by
      have h : ((childLH thetaAboveCell000022112101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112101) h)
    cover_subtree_4284ed2ee8d6
    cover_subtree_21c449726701

theorem cover_subtree_4e862092a132 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112102))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112102))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112102))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112102)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112102)) h)

theorem cover_subtree_aa7a39051514 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112102))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112102))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112102))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112102)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022112102))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022112102))) h))

theorem cover_subtree_bcfbc1ac2009 :
    adaptiveCoverCheck 7 thetaAboveCell000022112102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112102
    cover_subtree_4e862092a132
    cover_subtree_aa7a39051514
    (by
      have h : ((childHL thetaAboveCell000022112102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112102) h)
    (by
      have h : ((childHH thetaAboveCell000022112102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112102) h)

theorem cover_subtree_340b36315559 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112103))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112103))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022112103))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022112103))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022112103))) h))

theorem cover_subtree_3ea1443179e3 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112103))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112103))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022112103))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022112103))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022112103))) h))

theorem cover_subtree_333ca6341b52 :
    adaptiveCoverCheck 7 thetaAboveCell000022112103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112103
    cover_subtree_340b36315559
    cover_subtree_3ea1443179e3
    (by
      have h : ((childHL thetaAboveCell000022112103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112103) h)
    (by
      have h : ((childHH thetaAboveCell000022112103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112103) h)

theorem cover_subtree_0a317c2968a3 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002211)))
    cover_subtree_ff28352fdcbd
    cover_subtree_ecd8fe40a0e6
    cover_subtree_bcfbc1ac2009
    cover_subtree_333ca6341b52

theorem cover_subtree_0f6a5316da7f :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112110)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112110)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112110))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112110))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112110))) h))

theorem cover_subtree_8b21324e2245 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112110)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112110)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112110))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112110))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112110))) h))

theorem cover_subtree_2b3d980fd10a :
    adaptiveCoverCheck 7 thetaAboveCell000022112110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112110
    (by
      have h : ((childLL thetaAboveCell000022112110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112110) h)
    (by
      have h : ((childLH thetaAboveCell000022112110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112110) h)
    cover_subtree_0f6a5316da7f
    cover_subtree_8b21324e2245

theorem cover_subtree_3d8086490270 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112111)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112111)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112111))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112111))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112111))) h))

theorem cover_subtree_13b36b31ee50 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112111)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112111)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112111))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112111))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112111))) h))

theorem cover_subtree_fe061292783d :
    adaptiveCoverCheck 7 thetaAboveCell000022112111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112111
    (by
      have h : ((childLL thetaAboveCell000022112111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112111) h)
    (by
      have h : ((childLH thetaAboveCell000022112111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112111) h)
    cover_subtree_3d8086490270
    cover_subtree_13b36b31ee50

theorem cover_subtree_acdbdc38c196 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112112))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112112))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022112112))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022112112))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022112112))) h))

theorem cover_subtree_f4b1386a9f86 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112112))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112112))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022112112))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022112112))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022112112))) h))

theorem cover_subtree_280eb01136d6 :
    adaptiveCoverCheck 7 thetaAboveCell000022112112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112112
    cover_subtree_acdbdc38c196
    cover_subtree_f4b1386a9f86
    (by
      have h : ((childHL thetaAboveCell000022112112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112112) h)
    (by
      have h : ((childHH thetaAboveCell000022112112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112112) h)

theorem cover_subtree_3add30d6277d :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112113))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112113))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022112113))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022112113))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022112113))) h))

theorem cover_subtree_4b342ee841c3 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112113))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112113))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022112113))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022112113))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022112113))) h))

theorem cover_subtree_95d32084082d :
    adaptiveCoverCheck 7 thetaAboveCell000022112113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112113
    cover_subtree_3add30d6277d
    cover_subtree_4b342ee841c3
    (by
      have h : ((childHL thetaAboveCell000022112113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112113) h)
    (by
      have h : ((childHH thetaAboveCell000022112113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112113) h)

theorem cover_subtree_9112d0843a89 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002211)))
    cover_subtree_2b3d980fd10a
    cover_subtree_fe061292783d
    cover_subtree_280eb01136d6
    cover_subtree_95d32084082d

theorem e24KC2ThetaAboveLeaf0000221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002211))
    cover_subtree_0a317c2968a3
    cover_subtree_9112d0843a89
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112120 h)
        (by
          have h : (thetaAboveCell000022112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112121 h)
        (by
          have h : (thetaAboveCell000022112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112122 h)
        (by
          have h : (thetaAboveCell000022112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112130 h)
        (by
          have h : (thetaAboveCell000022112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112131 h)
        (by
          have h : (thetaAboveCell000022112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112132 h)
        (by
          have h : (thetaAboveCell000022112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112133 h))
theorem e24KC2ThetaAboveLeaf0000221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002211))) h)
theorem e24KC2ThetaAboveLeaf0000221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002211))) h)
theorem cover_subtree_c69725c188d3 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113000)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113000)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113000))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113000))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113000))) h))

theorem cover_subtree_a8d579475d23 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113000)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113000)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113000))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113000))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113000))) h))

theorem cover_subtree_560b815bd286 :
    adaptiveCoverCheck 7 thetaAboveCell000022113000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113000
    (by
      have h : ((childLL thetaAboveCell000022113000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113000) h)
    (by
      have h : ((childLH thetaAboveCell000022113000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113000) h)
    cover_subtree_c69725c188d3
    cover_subtree_a8d579475d23

theorem cover_subtree_995ab0851a0f :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113001)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113001)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113001))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113001))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113001))) h))

theorem cover_subtree_f5e3b9ffae68 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113001)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113001)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113001))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113001))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113001))) h))

theorem cover_subtree_e2b5567129eb :
    adaptiveCoverCheck 7 thetaAboveCell000022113001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113001
    (by
      have h : ((childLL thetaAboveCell000022113001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113001) h)
    (by
      have h : ((childLH thetaAboveCell000022113001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113001) h)
    cover_subtree_995ab0851a0f
    cover_subtree_f5e3b9ffae68

theorem cover_subtree_2a8071ef107e :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113002))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113002))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022113002))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022113002))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022113002))) h))

theorem cover_subtree_1f4e667d89aa :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113002))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113002))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022113002))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022113002))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022113002))) h))

theorem cover_subtree_cf43677b186a :
    adaptiveCoverCheck 7 thetaAboveCell000022113002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113002
    cover_subtree_2a8071ef107e
    cover_subtree_1f4e667d89aa
    (by
      have h : ((childHL thetaAboveCell000022113002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022113002) h)
    (by
      have h : ((childHH thetaAboveCell000022113002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022113002) h)

theorem cover_subtree_e06c4b38ee49 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113003))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113003))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022113003))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022113003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022113003))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022113003))) h))

theorem cover_subtree_5735fc3146a5 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113003))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113003))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113003))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022113003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022113003)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022113003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022113003)) h)

theorem cover_subtree_b9715c0ddc62 :
    adaptiveCoverCheck 7 thetaAboveCell000022113003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113003
    cover_subtree_e06c4b38ee49
    cover_subtree_5735fc3146a5
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113003)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113003)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113003)) h))

theorem cover_subtree_0338ef548092 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002211)))
    cover_subtree_560b815bd286
    cover_subtree_e2b5567129eb
    cover_subtree_cf43677b186a
    cover_subtree_b9715c0ddc62

theorem cover_subtree_8babef05283e :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113010)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113010)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113010))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113010))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113010))) h))

theorem cover_subtree_453a26c2a0ce :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113010)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113010)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113010))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113010))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113010))) h))

theorem cover_subtree_9a8d1e8ff5df :
    adaptiveCoverCheck 7 thetaAboveCell000022113010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113010
    (by
      have h : ((childLL thetaAboveCell000022113010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113010) h)
    (by
      have h : ((childLH thetaAboveCell000022113010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113010) h)
    cover_subtree_8babef05283e
    cover_subtree_453a26c2a0ce

theorem cover_subtree_d4f84dde625a :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113011)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113011)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113011))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113011))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113011))) h))

theorem cover_subtree_a97cdaa163bd :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113011)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113011)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113011))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113011))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113011))) h))

theorem cover_subtree_caad7b9ebe18 :
    adaptiveCoverCheck 7 thetaAboveCell000022113011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113011
    (by
      have h : ((childLL thetaAboveCell000022113011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113011) h)
    (by
      have h : ((childLH thetaAboveCell000022113011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113011) h)
    cover_subtree_d4f84dde625a
    cover_subtree_a97cdaa163bd

theorem cover_subtree_fbb8d3b85bf4 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113012))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113012))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113012))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022113012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022113012)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022113012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022113012)) h)

theorem cover_subtree_f025663eb4cc :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113012))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113012))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113012))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022113012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022113012)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022113012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022113012)) h)

theorem cover_subtree_6d9b8f942e07 :
    adaptiveCoverCheck 7 thetaAboveCell000022113012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113012
    cover_subtree_fbb8d3b85bf4
    cover_subtree_f025663eb4cc
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113012)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113012)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113012)) h))

theorem cover_subtree_c85e1b57b2c5 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113013))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113013))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113013))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022113013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022113013)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022113013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022113013)) h)

theorem cover_subtree_a12be2bf4817 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113013))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113013))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113013))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022113013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022113013)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022113013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022113013)) h)

theorem cover_subtree_d1382a844a10 :
    adaptiveCoverCheck 7 thetaAboveCell000022113013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113013
    cover_subtree_c85e1b57b2c5
    cover_subtree_a12be2bf4817
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113013)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113013)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113013)) h))

theorem cover_subtree_d4d29d86cd96 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002211)))
    cover_subtree_9a8d1e8ff5df
    cover_subtree_caad7b9ebe18
    cover_subtree_6d9b8f942e07
    cover_subtree_d1382a844a10

theorem e24KC2ThetaAboveLeaf0000221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002211))
    cover_subtree_0338ef548092
    cover_subtree_d4d29d86cd96
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113020 h)
        (by
          have h : (thetaAboveCell000022113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113021 h)
        (by
          have h : (thetaAboveCell000022113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113022 h)
        (by
          have h : (thetaAboveCell000022113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113030 h)
        (by
          have h : (thetaAboveCell000022113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113031 h)
        (by
          have h : (thetaAboveCell000022113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113032 h)
        (by
          have h : (thetaAboveCell000022113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113033 h))
theorem cover_subtree_836d962e65ac :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113100)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113100)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113100))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113100))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113100))) h))

theorem cover_subtree_ecf6c7f90571 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113100)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113100)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113100))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113100))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113100))) h))

theorem cover_subtree_fa2b1e57d306 :
    adaptiveCoverCheck 7 thetaAboveCell000022113100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113100
    (by
      have h : ((childLL thetaAboveCell000022113100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113100) h)
    (by
      have h : ((childLH thetaAboveCell000022113100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113100) h)
    cover_subtree_836d962e65ac
    cover_subtree_ecf6c7f90571

theorem cover_subtree_2c032bc482bc :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113101)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113101)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113101))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113101))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113101))) h))

theorem cover_subtree_3eddb0efc253 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113101)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113101)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113101))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113101))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113101))) h))

theorem cover_subtree_cbdd15c92455 :
    adaptiveCoverCheck 7 thetaAboveCell000022113101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113101
    (by
      have h : ((childLL thetaAboveCell000022113101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113101) h)
    (by
      have h : ((childLH thetaAboveCell000022113101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113101) h)
    cover_subtree_2c032bc482bc
    cover_subtree_3eddb0efc253

theorem cover_subtree_e867c54455aa :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113102))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113102))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113102))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022113102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022113102)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022113102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022113102)) h)

theorem cover_subtree_d8e5977bc823 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113102))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113102))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113102))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022113102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022113102)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022113102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022113102)) h)

theorem cover_subtree_81e578425a2e :
    adaptiveCoverCheck 7 thetaAboveCell000022113102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113102
    cover_subtree_e867c54455aa
    cover_subtree_d8e5977bc823
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113102)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113102)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113102)) h))

theorem cover_subtree_6af7504512c8 :
    adaptiveCoverCheck 7 thetaAboveCell000022113103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113103)
        (by
          have h : ((childLL (childLL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113103)
        (by
          have h : ((childLL (childLH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113103)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113103)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113103)) h))

theorem cover_subtree_dc05a5cb4d61 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002211)))
    cover_subtree_fa2b1e57d306
    cover_subtree_cbdd15c92455
    cover_subtree_81e578425a2e
    cover_subtree_6af7504512c8

theorem cover_subtree_fcbdf3a9e595 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113110)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113110)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113110))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113110))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113110))) h))

theorem cover_subtree_2828e56e478f :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113110)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113110)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113110))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113110))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113110))) h))

theorem cover_subtree_15fb86545eea :
    adaptiveCoverCheck 7 thetaAboveCell000022113110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113110
    (by
      have h : ((childLL thetaAboveCell000022113110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113110) h)
    (by
      have h : ((childLH thetaAboveCell000022113110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113110) h)
    cover_subtree_fcbdf3a9e595
    cover_subtree_2828e56e478f

theorem cover_subtree_0f38c8258b2e :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113111)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113111)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113111))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113111))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113111))) h))

theorem cover_subtree_13fc46665967 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113111)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113111)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113111))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113111))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113111))) h))

theorem cover_subtree_83c447d13cd0 :
    adaptiveCoverCheck 7 thetaAboveCell000022113111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113111
    (by
      have h : ((childLL thetaAboveCell000022113111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113111) h)
    (by
      have h : ((childLH thetaAboveCell000022113111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113111) h)
    cover_subtree_0f38c8258b2e
    cover_subtree_13fc46665967

theorem cover_subtree_02c32f65c578 :
    adaptiveCoverCheck 7 thetaAboveCell000022113112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113112)
        (by
          have h : ((childLL (childLL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113112)
        (by
          have h : ((childLL (childLH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113112)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113112)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113112)) h))

theorem cover_subtree_74079318656f :
    adaptiveCoverCheck 7 thetaAboveCell000022113113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113113)
        (by
          have h : ((childLL (childLL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113113)
        (by
          have h : ((childLL (childLH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113113)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113113)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113113)) h))

theorem cover_subtree_6a41f1f44284 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002211)))
    cover_subtree_15fb86545eea
    cover_subtree_83c447d13cd0
    cover_subtree_02c32f65c578
    cover_subtree_74079318656f

theorem e24KC2ThetaAboveLeaf0000221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002211))
    cover_subtree_dc05a5cb4d61
    cover_subtree_6a41f1f44284
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113120 h)
        (by
          have h : (thetaAboveCell000022113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113121 h)
        (by
          have h : (thetaAboveCell000022113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113122 h)
        (by
          have h : (thetaAboveCell000022113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113130 h)
        (by
          have h : (thetaAboveCell000022113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113131 h)
        (by
          have h : (thetaAboveCell000022113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113132 h)
        (by
          have h : (thetaAboveCell000022113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113133 h))
theorem e24KC2ThetaAboveLeaf0000221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002211))) h)
theorem e24KC2ThetaAboveLeaf0000221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002211))) h)
theorem e24KC2ThetaAboveLeaf0000230002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00002300))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00002300))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00002300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023000220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000220 h)
        (by
          have h : (thetaAboveCell000023000221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000221 h)
        (by
          have h : (thetaAboveCell000023000222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000222 h)
        (by
          have h : (thetaAboveCell000023000223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023000230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000230 h)
        (by
          have h : (thetaAboveCell000023000231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000231 h)
        (by
          have h : (thetaAboveCell000023000232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000232 h)
        (by
          have h : (thetaAboveCell000023000233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000233 h))
theorem e24KC2ThetaAboveLeaf0000230003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00002300))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00002300))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00002300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023000320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000320 h)
        (by
          have h : (thetaAboveCell000023000321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000321 h)
        (by
          have h : (thetaAboveCell000023000322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000322 h)
        (by
          have h : (thetaAboveCell000023000323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023000330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000330 h)
        (by
          have h : (thetaAboveCell000023000331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000331 h)
        (by
          have h : (thetaAboveCell000023000332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000332 h)
        (by
          have h : (thetaAboveCell000023000333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000333 h))
theorem e24KC2ThetaAboveLeaf0000230012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00002300))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00002300))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00002300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023001220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001220 h)
        (by
          have h : (thetaAboveCell000023001221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001221 h)
        (by
          have h : (thetaAboveCell000023001222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001222 h)
        (by
          have h : (thetaAboveCell000023001223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLH
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023001230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001230 h)
        (by
          have h : (thetaAboveCell000023001231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001231 h)
        (by
          have h : (thetaAboveCell000023001232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001232 h)
        (by
          have h : (thetaAboveCell000023001233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001233 h))
theorem e24KC2ThetaAboveLeaf0000230013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00002300))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00002300))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00002300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLH
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023001320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001320 h)
        (by
          have h : (thetaAboveCell000023001321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001321 h)
        (by
          have h : (thetaAboveCell000023001322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001322 h)
        (by
          have h : (thetaAboveCell000023001323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023001330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001330 h)
        (by
          have h : (thetaAboveCell000023001331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001331 h)
        (by
          have h : (thetaAboveCell000023001332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001332 h)
        (by
          have h : (thetaAboveCell000023001333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001333 h))

end PartE
end GerverSofa

end

end

end
