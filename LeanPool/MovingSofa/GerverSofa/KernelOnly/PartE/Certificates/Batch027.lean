/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchB39d17cf54d27511`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC6 explicit proof-producing certificate batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells802ef10e9d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0000)))
/-- Subcell `00002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0000)))
/-- Subcell `00003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0000)))
/-- Subcell `00003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0000)))
/-- Subcell `000023102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002310)))
/-- Subcell `000023102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002310)))
/-- Subcell `000023103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002310)))
/-- Subcell `000023103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002310)))
/-- Subcell `000023110220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00002311)))
/-- Subcell `000023110221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00002311)))
/-- Subcell `000023110222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00002311)))
/-- Subcell `000023110223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00002311)))
/-- Subcell `000023110230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00002311)))
/-- Subcell `000023110231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00002311)))
/-- Subcell `000023110232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00002311)))
/-- Subcell `000023110233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00002311)))
/-- Subcell `000023110320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00002311)))
/-- Subcell `000023110321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00002311)))
/-- Subcell `000023110322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00002311)))
/-- Subcell `000023110323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00002311)))
/-- Subcell `000023110330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00002311)))
/-- Subcell `000023110331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00002311)))
/-- Subcell `000023110332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00002311)))
/-- Subcell `000023110333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00002311)))
/-- Subcell `000023111220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00002311)))
/-- Subcell `000023111221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00002311)))
/-- Subcell `000023111222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00002311)))
/-- Subcell `000023111223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00002311)))
/-- Subcell `000023111230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaAboveCell00002311)))
/-- Subcell `000023111231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaAboveCell00002311)))
/-- Subcell `000023111232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaAboveCell00002311)))
/-- Subcell `000023111233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaAboveCell00002311)))
/-- Subcell `000023111320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaAboveCell00002311)))
/-- Subcell `000023111321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaAboveCell00002311)))
/-- Subcell `000023111322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaAboveCell00002311)))
/-- Subcell `000023111323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaAboveCell00002311)))
/-- Subcell `000023111330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaAboveCell00002311)))
/-- Subcell `000023111331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaAboveCell00002311)))
/-- Subcell `000023111332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaAboveCell00002311)))
/-- Subcell `000023111333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaAboveCell00002311)))
/-- Subcell `000023112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002311)))
/-- Subcell `000023112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002311)))
/-- Subcell `000023113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002311)))
/-- Subcell `000023113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000023113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002311)))
/-- Subcell `000032000220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00003200)))
/-- Subcell `000032000221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00003200)))
/-- Subcell `000032000222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00003200)))
/-- Subcell `000032000223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00003200)))
/-- Subcell `000032000230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00003200)))
/-- Subcell `000032000231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00003200)))
/-- Subcell `000032000232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00003200)))
/-- Subcell `000032000233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00003200)))
/-- Subcell `000032000320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00003200)))
/-- Subcell `000032000321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00003200)))
/-- Subcell `000032000322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00003200)))
/-- Subcell `000032000323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00003200)))
/-- Subcell `000032000330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00003200)))
/-- Subcell `000032000331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00003200)))
/-- Subcell `000032000332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00003200)))
/-- Subcell `000032000333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00003200)))
/-- Subcell `000032001220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032001220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00003200)))
/-- Subcell `000032001221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032001221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00003200)))
/-- Subcell `000032001222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032001222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00003200)))
/-- Subcell `000032001223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032001223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00003200)))
/-- Subcell `000032002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003200)))
/-- Subcell `000032002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003200)))
/-- Subcell `000032003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003200)))
/-- Subcell `000032003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003200)))
/-- Subcell `000032003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003200)))

end CertificateCells802ef10e9d

open CertificateCells802ef10e9d
theorem cover_subtree_f27aed8d7652 :
    adaptiveCoverCheck 7 thetaAboveCell000023102000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102000
    (by
      have h : ((childLL thetaAboveCell000023102000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102000) h)
    (by
      have h : ((childLH thetaAboveCell000023102000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102000) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102000)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102000)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102000)) h))

theorem cover_subtree_005f989c43cb :
    adaptiveCoverCheck 7 thetaAboveCell000023102001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102001
    (by
      have h : ((childLL thetaAboveCell000023102001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102001) h)
    (by
      have h : ((childLH thetaAboveCell000023102001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102001) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102001)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102001)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102001)) h))

theorem cover_subtree_9ea21eaf3506 :
    adaptiveCoverCheck 7 thetaAboveCell000023102002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102002)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102002)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102002)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102002)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102002)) h))

theorem cover_subtree_aecd625dd7fb :
    adaptiveCoverCheck 7 thetaAboveCell000023102003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102003)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102003)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102003)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102003)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102003)) h))

theorem cover_subtree_77a434675cac :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002310)))
    cover_subtree_f27aed8d7652
    cover_subtree_005f989c43cb
    cover_subtree_9ea21eaf3506
    cover_subtree_aecd625dd7fb

theorem cover_subtree_422f11b7507e :
    adaptiveCoverCheck 7 thetaAboveCell000023102010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102010
    (by
      have h : ((childLL thetaAboveCell000023102010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102010) h)
    (by
      have h : ((childLH thetaAboveCell000023102010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102010) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102010)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102010)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102010)) h))

theorem cover_subtree_9333e7948d29 :
    adaptiveCoverCheck 7 thetaAboveCell000023102011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102011
    (by
      have h : ((childLL thetaAboveCell000023102011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102011) h)
    (by
      have h : ((childLH thetaAboveCell000023102011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102011) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102011)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102011)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102011)) h))

theorem cover_subtree_0e2f446f3080 :
    adaptiveCoverCheck 7 thetaAboveCell000023102012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102012)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102012)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102012)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102012)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102012)) h))

theorem cover_subtree_07cb153dceed :
    adaptiveCoverCheck 7 thetaAboveCell000023102013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102013)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102013)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102013)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102013)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102013)) h))

theorem cover_subtree_334813029f45 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00002310)))
    cover_subtree_422f11b7507e
    cover_subtree_9333e7948d29
    cover_subtree_0e2f446f3080
    cover_subtree_07cb153dceed

theorem cover_subtree_c82ade123eba :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102020
        (by
          have h : ((childLL thetaAboveCell000023102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102020) h)
        (by
          have h : ((childLH thetaAboveCell000023102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102020) h)
        (by
          have h : ((childHL thetaAboveCell000023102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102020) h)
        (by
          have h : ((childHH thetaAboveCell000023102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102021
        (by
          have h : ((childLL thetaAboveCell000023102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102021) h)
        (by
          have h : ((childLH thetaAboveCell000023102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102021) h)
        (by
          have h : ((childHL thetaAboveCell000023102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102021) h)
        (by
          have h : ((childHH thetaAboveCell000023102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102021) h))
    (by
      have h : (thetaAboveCell000023102022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102022 h)
    (by
      have h : (thetaAboveCell000023102023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102023 h)

theorem cover_subtree_b2c2dad45076 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102030
        (by
          have h : ((childLL thetaAboveCell000023102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102030) h)
        (by
          have h : ((childLH thetaAboveCell000023102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102030) h)
        (by
          have h : ((childHL thetaAboveCell000023102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102030) h)
        (by
          have h : ((childHH thetaAboveCell000023102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102031
        (by
          have h : ((childLL thetaAboveCell000023102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102031) h)
        (by
          have h : ((childLH thetaAboveCell000023102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102031) h)
        (by
          have h : ((childHL thetaAboveCell000023102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102031) h)
        (by
          have h : ((childHH thetaAboveCell000023102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102031) h))
    (by
      have h : (thetaAboveCell000023102032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102032 h)
    (by
      have h : (thetaAboveCell000023102033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102033 h)

theorem e24KC2ThetaAboveLeaf0000231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002310))
    cover_subtree_77a434675cac
    cover_subtree_334813029f45
    cover_subtree_c82ade123eba
    cover_subtree_b2c2dad45076
theorem cover_subtree_d0ee7bfc8527 :
    adaptiveCoverCheck 7 thetaAboveCell000023102100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102100
    (by
      have h : ((childLL thetaAboveCell000023102100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102100) h)
    (by
      have h : ((childLH thetaAboveCell000023102100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102100) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102100)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102100)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102100)) h))

theorem cover_subtree_58a66e346033 :
    adaptiveCoverCheck 7 thetaAboveCell000023102101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102101
    (by
      have h : ((childLL thetaAboveCell000023102101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102101) h)
    (by
      have h : ((childLH thetaAboveCell000023102101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102101) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102101)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102101)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102101)) h))

theorem cover_subtree_c17867007896 :
    adaptiveCoverCheck 7 thetaAboveCell000023102102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102102)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102102)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102102)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102102)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102102)) h))

theorem cover_subtree_70f834eb3976 :
    adaptiveCoverCheck 7 thetaAboveCell000023102103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102103)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102103)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102103)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102103)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102103)) h))

theorem cover_subtree_a226aa051b7b :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002310)))
    cover_subtree_d0ee7bfc8527
    cover_subtree_58a66e346033
    cover_subtree_c17867007896
    cover_subtree_70f834eb3976

theorem cover_subtree_71a49837eadf :
    adaptiveCoverCheck 7 thetaAboveCell000023102112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102112)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102112)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102112)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102112)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102112)) h))

theorem cover_subtree_5a86501aa891 :
    adaptiveCoverCheck 7 thetaAboveCell000023102113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102113)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102113)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102113)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102113)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102113)) h))

theorem cover_subtree_1d4344731b0b :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102110
        (by
          have h : ((childLL thetaAboveCell000023102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102110) h)
        (by
          have h : ((childLH thetaAboveCell000023102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102110) h)
        (by
          have h : ((childHL thetaAboveCell000023102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102110) h)
        (by
          have h : ((childHH thetaAboveCell000023102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102111
        (by
          have h : ((childLL thetaAboveCell000023102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102111) h)
        (by
          have h : ((childLH thetaAboveCell000023102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102111) h)
        (by
          have h : ((childHL thetaAboveCell000023102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102111) h)
        (by
          have h : ((childHH thetaAboveCell000023102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102111) h))
    cover_subtree_71a49837eadf
    cover_subtree_5a86501aa891

theorem cover_subtree_3bdba90bbb0c :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102120
        (by
          have h : ((childLL thetaAboveCell000023102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102120) h)
        (by
          have h : ((childLH thetaAboveCell000023102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102120) h)
        (by
          have h : ((childHL thetaAboveCell000023102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102120) h)
        (by
          have h : ((childHH thetaAboveCell000023102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102121
        (by
          have h : ((childLL thetaAboveCell000023102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102121) h)
        (by
          have h : ((childLH thetaAboveCell000023102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102121) h)
        (by
          have h : ((childHL thetaAboveCell000023102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102121) h)
        (by
          have h : ((childHH thetaAboveCell000023102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102121) h))
    (by
      have h : (thetaAboveCell000023102122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102122 h)
    (by
      have h : (thetaAboveCell000023102123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102123 h)

theorem cover_subtree_f8da85ca8892 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102130
        (by
          have h : ((childLL thetaAboveCell000023102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102130) h)
        (by
          have h : ((childLH thetaAboveCell000023102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102130) h)
        (by
          have h : ((childHL thetaAboveCell000023102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102130) h)
        (by
          have h : ((childHH thetaAboveCell000023102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102131
        (by
          have h : ((childLL thetaAboveCell000023102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102131) h)
        (by
          have h : ((childLH thetaAboveCell000023102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102131) h)
        (by
          have h : ((childHL thetaAboveCell000023102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102131) h)
        (by
          have h : ((childHH thetaAboveCell000023102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102131) h))
    (by
      have h : (thetaAboveCell000023102132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102132 h)
    (by
      have h : (thetaAboveCell000023102133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102133 h)

theorem e24KC2ThetaAboveLeaf0000231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002310))
    cover_subtree_a226aa051b7b
    cover_subtree_1d4344731b0b
    cover_subtree_3bdba90bbb0c
    cover_subtree_f8da85ca8892
theorem e24KC2ThetaAboveLeaf0000231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002310))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002310))) h)
theorem e24KC2ThetaAboveLeaf0000231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002310))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002310))) h)
theorem cover_subtree_786f313d71e4 :
    adaptiveCoverCheck 7 thetaAboveCell000023103002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103002)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103002)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103002)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103002)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103002)) h))

theorem cover_subtree_7c7cbd1b1de9 :
    adaptiveCoverCheck 7 thetaAboveCell000023103003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103003)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103003)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103003)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103003)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103003)) h))

theorem cover_subtree_e95dc4fe2400 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103000
        (by
          have h : ((childLL thetaAboveCell000023103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103000) h)
        (by
          have h : ((childLH thetaAboveCell000023103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103000) h)
        (by
          have h : ((childHL thetaAboveCell000023103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103000) h)
        (by
          have h : ((childHH thetaAboveCell000023103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103001
        (by
          have h : ((childLL thetaAboveCell000023103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103001) h)
        (by
          have h : ((childLH thetaAboveCell000023103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103001) h)
        (by
          have h : ((childHL thetaAboveCell000023103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103001) h)
        (by
          have h : ((childHH thetaAboveCell000023103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103001) h))
    cover_subtree_786f313d71e4
    cover_subtree_7c7cbd1b1de9

theorem cover_subtree_d1ef0fda9310 :
    adaptiveCoverCheck 7 thetaAboveCell000023103012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103012)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103012)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103012)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103012)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103012)) h))

theorem cover_subtree_334bbbdc1a85 :
    adaptiveCoverCheck 7 thetaAboveCell000023103013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103013)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103013)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103013)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103013)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103013)) h))

theorem cover_subtree_1b4b2c805488 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103010
        (by
          have h : ((childLL thetaAboveCell000023103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103010) h)
        (by
          have h : ((childLH thetaAboveCell000023103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103010) h)
        (by
          have h : ((childHL thetaAboveCell000023103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103010) h)
        (by
          have h : ((childHH thetaAboveCell000023103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103011
        (by
          have h : ((childLL thetaAboveCell000023103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103011) h)
        (by
          have h : ((childLH thetaAboveCell000023103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103011) h)
        (by
          have h : ((childHL thetaAboveCell000023103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103011) h)
        (by
          have h : ((childHH thetaAboveCell000023103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103011) h))
    cover_subtree_d1ef0fda9310
    cover_subtree_334bbbdc1a85

theorem cover_subtree_d023ef13133b :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103020
        (by
          have h : ((childLL thetaAboveCell000023103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103020) h)
        (by
          have h : ((childLH thetaAboveCell000023103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103020) h)
        (by
          have h : ((childHL thetaAboveCell000023103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103020) h)
        (by
          have h : ((childHH thetaAboveCell000023103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103021
        (by
          have h : ((childLL thetaAboveCell000023103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103021) h)
        (by
          have h : ((childLH thetaAboveCell000023103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103021) h)
        (by
          have h : ((childHL thetaAboveCell000023103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103021) h)
        (by
          have h : ((childHH thetaAboveCell000023103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103021) h))
    (by
      have h : (thetaAboveCell000023103022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103022 h)
    (by
      have h : (thetaAboveCell000023103023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103023 h)

theorem cover_subtree_8107f33bf217 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103030
        (by
          have h : ((childLL thetaAboveCell000023103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103030) h)
        (by
          have h : ((childLH thetaAboveCell000023103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103030) h)
        (by
          have h : ((childHL thetaAboveCell000023103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103030) h)
        (by
          have h : ((childHH thetaAboveCell000023103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103031
        (by
          have h : ((childLL thetaAboveCell000023103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103031) h)
        (by
          have h : ((childLH thetaAboveCell000023103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103031) h)
        (by
          have h : ((childHL thetaAboveCell000023103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103031) h)
        (by
          have h : ((childHH thetaAboveCell000023103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103031) h))
    (by
      have h : (thetaAboveCell000023103032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103032 h)
    (by
      have h : (thetaAboveCell000023103033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103033 h)

theorem e24KC2ThetaAboveLeaf0000231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002310))
    cover_subtree_e95dc4fe2400
    cover_subtree_1b4b2c805488
    cover_subtree_d023ef13133b
    cover_subtree_8107f33bf217
theorem cover_subtree_e7898c3dadb7 :
    adaptiveCoverCheck 7 thetaAboveCell000023103102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103102)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103102)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103102)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103102)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103102)) h))

theorem cover_subtree_76677b2fe65f :
    adaptiveCoverCheck 7 thetaAboveCell000023103103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103103)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103103)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103103)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103103)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103103)) h))

theorem cover_subtree_b293a3c8540f :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103100
        (by
          have h : ((childLL thetaAboveCell000023103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103100) h)
        (by
          have h : ((childLH thetaAboveCell000023103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103100) h)
        (by
          have h : ((childHL thetaAboveCell000023103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103100) h)
        (by
          have h : ((childHH thetaAboveCell000023103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103101
        (by
          have h : ((childLL thetaAboveCell000023103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103101) h)
        (by
          have h : ((childLH thetaAboveCell000023103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103101) h)
        (by
          have h : ((childHL thetaAboveCell000023103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103101) h)
        (by
          have h : ((childHH thetaAboveCell000023103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103101) h))
    cover_subtree_e7898c3dadb7
    cover_subtree_76677b2fe65f

theorem cover_subtree_a17e19b0274e :
    adaptiveCoverCheck 7 thetaAboveCell000023103112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103112)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103112)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103112)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103112)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103112)) h))

theorem cover_subtree_e650c47410b7 :
    adaptiveCoverCheck 7 thetaAboveCell000023103113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103113)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103113)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103113)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103113)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103113)) h))

theorem cover_subtree_d40c83c06c06 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103110
        (by
          have h : ((childLL thetaAboveCell000023103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103110) h)
        (by
          have h : ((childLH thetaAboveCell000023103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103110) h)
        (by
          have h : ((childHL thetaAboveCell000023103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103110) h)
        (by
          have h : ((childHH thetaAboveCell000023103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103111
        (by
          have h : ((childLL thetaAboveCell000023103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103111) h)
        (by
          have h : ((childLH thetaAboveCell000023103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103111) h)
        (by
          have h : ((childHL thetaAboveCell000023103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103111) h)
        (by
          have h : ((childHH thetaAboveCell000023103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103111) h))
    cover_subtree_a17e19b0274e
    cover_subtree_e650c47410b7

theorem cover_subtree_759d6e2f1f21 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103120
        (by
          have h : ((childLL thetaAboveCell000023103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103120) h)
        (by
          have h : ((childLH thetaAboveCell000023103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103120) h)
        (by
          have h : ((childHL thetaAboveCell000023103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103120) h)
        (by
          have h : ((childHH thetaAboveCell000023103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103121
        (by
          have h : ((childLL thetaAboveCell000023103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103121) h)
        (by
          have h : ((childLH thetaAboveCell000023103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103121) h)
        (by
          have h : ((childHL thetaAboveCell000023103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103121) h)
        (by
          have h : ((childHH thetaAboveCell000023103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103121) h))
    (by
      have h : (thetaAboveCell000023103122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103122 h)
    (by
      have h : (thetaAboveCell000023103123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103123 h)

theorem cover_subtree_695ff4e0f9a2 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103130
        (by
          have h : ((childLL thetaAboveCell000023103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103130) h)
        (by
          have h : ((childLH thetaAboveCell000023103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103130) h)
        (by
          have h : ((childHL thetaAboveCell000023103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103130) h)
        (by
          have h : ((childHH thetaAboveCell000023103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103131
        (by
          have h : ((childLL thetaAboveCell000023103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103131) h)
        (by
          have h : ((childLH thetaAboveCell000023103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103131) h)
        (by
          have h : ((childHL thetaAboveCell000023103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103131) h)
        (by
          have h : ((childHH thetaAboveCell000023103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103131) h))
    (by
      have h : (thetaAboveCell000023103132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103132 h)
    (by
      have h : (thetaAboveCell000023103133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103133 h)

theorem e24KC2ThetaAboveLeaf0000231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002310))
    cover_subtree_b293a3c8540f
    cover_subtree_d40c83c06c06
    cover_subtree_759d6e2f1f21
    cover_subtree_695ff4e0f9a2
theorem e24KC2ThetaAboveLeaf0000231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002310))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002310))) h)
theorem e24KC2ThetaAboveLeaf0000231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002310))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002310))) h)
theorem e24KC2ThetaAboveLeaf0000231102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00002311))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00002311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023110220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110220 h)
        (by
          have h : (thetaAboveCell000023110221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110221 h)
        (by
          have h : (thetaAboveCell000023110222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110222 h)
        (by
          have h : (thetaAboveCell000023110223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023110230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110230 h)
        (by
          have h : (thetaAboveCell000023110231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110231 h)
        (by
          have h : (thetaAboveCell000023110232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110232 h)
        (by
          have h : (thetaAboveCell000023110233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110233 h))
theorem e24KC2ThetaAboveLeaf0000231103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00002311))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00002311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023110320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110320 h)
        (by
          have h : (thetaAboveCell000023110321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110321 h)
        (by
          have h : (thetaAboveCell000023110322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110322 h)
        (by
          have h : (thetaAboveCell000023110323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023110330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110330 h)
        (by
          have h : (thetaAboveCell000023110331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110331 h)
        (by
          have h : (thetaAboveCell000023110332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110332 h)
        (by
          have h : (thetaAboveCell000023110333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110333 h))
theorem e24KC2ThetaAboveLeaf0000231112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00002311))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00002311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023111220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111220 h)
        (by
          have h : (thetaAboveCell000023111221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111221 h)
        (by
          have h : (thetaAboveCell000023111222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111222 h)
        (by
          have h : (thetaAboveCell000023111223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLH
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023111230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111230 h)
        (by
          have h : (thetaAboveCell000023111231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111231 h)
        (by
          have h : (thetaAboveCell000023111232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111232 h)
        (by
          have h : (thetaAboveCell000023111233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111233 h))
theorem e24KC2ThetaAboveLeaf0000231113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00002311))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00002311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLH
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023111320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111320 h)
        (by
          have h : (thetaAboveCell000023111321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111321 h)
        (by
          have h : (thetaAboveCell000023111322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111322 h)
        (by
          have h : (thetaAboveCell000023111323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023111330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111330 h)
        (by
          have h : (thetaAboveCell000023111331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111331 h)
        (by
          have h : (thetaAboveCell000023111332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111332 h)
        (by
          have h : (thetaAboveCell000023111333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111333 h))
theorem cover_subtree_b3ebd2cd2770 :
    adaptiveCoverCheck 7 thetaAboveCell000023112002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112002)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112002)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112002)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112002)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112002)) h))

theorem cover_subtree_f788d0e2a5ae :
    adaptiveCoverCheck 7 thetaAboveCell000023112003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112003)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112003)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112003)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112003)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112003)) h))

theorem cover_subtree_7f7afb8d0a4d :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112000
        (by
          have h : ((childLL thetaAboveCell000023112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112000) h)
        (by
          have h : ((childLH thetaAboveCell000023112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112000) h)
        (by
          have h : ((childHL thetaAboveCell000023112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112000) h)
        (by
          have h : ((childHH thetaAboveCell000023112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112001
        (by
          have h : ((childLL thetaAboveCell000023112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112001) h)
        (by
          have h : ((childLH thetaAboveCell000023112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112001) h)
        (by
          have h : ((childHL thetaAboveCell000023112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112001) h)
        (by
          have h : ((childHH thetaAboveCell000023112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112001) h))
    cover_subtree_b3ebd2cd2770
    cover_subtree_f788d0e2a5ae

theorem cover_subtree_074cd1f5f52c :
    adaptiveCoverCheck 7 thetaAboveCell000023112012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112012)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112012)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112012)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112012)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112012)) h))

theorem cover_subtree_dfbe90b65883 :
    adaptiveCoverCheck 7 thetaAboveCell000023112013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112013)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112013)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112013)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112013)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112013)) h))

theorem cover_subtree_20dd499bd364 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112010
        (by
          have h : ((childLL thetaAboveCell000023112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112010) h)
        (by
          have h : ((childLH thetaAboveCell000023112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112010) h)
        (by
          have h : ((childHL thetaAboveCell000023112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112010) h)
        (by
          have h : ((childHH thetaAboveCell000023112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112011
        (by
          have h : ((childLL thetaAboveCell000023112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112011) h)
        (by
          have h : ((childLH thetaAboveCell000023112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112011) h)
        (by
          have h : ((childHL thetaAboveCell000023112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112011) h)
        (by
          have h : ((childHH thetaAboveCell000023112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112011) h))
    cover_subtree_074cd1f5f52c
    cover_subtree_dfbe90b65883

theorem cover_subtree_97430f27dc25 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112020
        (by
          have h : ((childLL thetaAboveCell000023112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112020) h)
        (by
          have h : ((childLH thetaAboveCell000023112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112020) h)
        (by
          have h : ((childHL thetaAboveCell000023112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112020) h)
        (by
          have h : ((childHH thetaAboveCell000023112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112021
        (by
          have h : ((childLL thetaAboveCell000023112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112021) h)
        (by
          have h : ((childLH thetaAboveCell000023112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112021) h)
        (by
          have h : ((childHL thetaAboveCell000023112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112021) h)
        (by
          have h : ((childHH thetaAboveCell000023112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112021) h))
    (by
      have h : (thetaAboveCell000023112022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112022 h)
    (by
      have h : (thetaAboveCell000023112023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112023 h)

theorem cover_subtree_8ea35ca64562 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112030
        (by
          have h : ((childLL thetaAboveCell000023112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112030) h)
        (by
          have h : ((childLH thetaAboveCell000023112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112030) h)
        (by
          have h : ((childHL thetaAboveCell000023112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112030) h)
        (by
          have h : ((childHH thetaAboveCell000023112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112031
        (by
          have h : ((childLL thetaAboveCell000023112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112031) h)
        (by
          have h : ((childLH thetaAboveCell000023112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112031) h)
        (by
          have h : ((childHL thetaAboveCell000023112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112031) h)
        (by
          have h : ((childHH thetaAboveCell000023112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112031) h))
    (by
      have h : (thetaAboveCell000023112032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112032 h)
    (by
      have h : (thetaAboveCell000023112033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112033 h)

theorem e24KC2ThetaAboveLeaf0000231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002311))
    cover_subtree_7f7afb8d0a4d
    cover_subtree_20dd499bd364
    cover_subtree_97430f27dc25
    cover_subtree_8ea35ca64562
theorem cover_subtree_bb7934ab6a6d :
    adaptiveCoverCheck 7 thetaAboveCell000023112102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112102)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112102)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112102)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112102)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112102)) h))

theorem cover_subtree_f960ce5080b6 :
    adaptiveCoverCheck 7 thetaAboveCell000023112103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112103)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112103)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112103)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112103)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112103)) h))

theorem cover_subtree_be8b495598ef :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112100
        (by
          have h : ((childLL thetaAboveCell000023112100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112100) h)
        (by
          have h : ((childLH thetaAboveCell000023112100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112100) h)
        (by
          have h : ((childHL thetaAboveCell000023112100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112100) h)
        (by
          have h : ((childHH thetaAboveCell000023112100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112101
        (by
          have h : ((childLL thetaAboveCell000023112101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112101) h)
        (by
          have h : ((childLH thetaAboveCell000023112101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112101) h)
        (by
          have h : ((childHL thetaAboveCell000023112101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112101) h)
        (by
          have h : ((childHH thetaAboveCell000023112101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112101) h))
    cover_subtree_bb7934ab6a6d
    cover_subtree_f960ce5080b6

theorem cover_subtree_c24cbad7c860 :
    adaptiveCoverCheck 7 thetaAboveCell000023112112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112112)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112112)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112112)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112112)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112112)) h))

theorem cover_subtree_5030364bf316 :
    adaptiveCoverCheck 7 thetaAboveCell000023112113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112113)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112113)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112113)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112113)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112113)) h))

theorem cover_subtree_b9cce4a71b20 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112110
        (by
          have h : ((childLL thetaAboveCell000023112110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112110) h)
        (by
          have h : ((childLH thetaAboveCell000023112110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112110) h)
        (by
          have h : ((childHL thetaAboveCell000023112110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112110) h)
        (by
          have h : ((childHH thetaAboveCell000023112110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112111
        (by
          have h : ((childLL thetaAboveCell000023112111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112111) h)
        (by
          have h : ((childLH thetaAboveCell000023112111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112111) h)
        (by
          have h : ((childHL thetaAboveCell000023112111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112111) h)
        (by
          have h : ((childHH thetaAboveCell000023112111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112111) h))
    cover_subtree_c24cbad7c860
    cover_subtree_5030364bf316

theorem cover_subtree_f376dd8d0235 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112120
        (by
          have h : ((childLL thetaAboveCell000023112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112120) h)
        (by
          have h : ((childLH thetaAboveCell000023112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112120) h)
        (by
          have h : ((childHL thetaAboveCell000023112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112120) h)
        (by
          have h : ((childHH thetaAboveCell000023112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112121
        (by
          have h : ((childLL thetaAboveCell000023112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112121) h)
        (by
          have h : ((childLH thetaAboveCell000023112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112121) h)
        (by
          have h : ((childHL thetaAboveCell000023112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112121) h)
        (by
          have h : ((childHH thetaAboveCell000023112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112121) h))
    (by
      have h : (thetaAboveCell000023112122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112122 h)
    (by
      have h : (thetaAboveCell000023112123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112123 h)

theorem cover_subtree_a9dfb54a5534 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112130
        (by
          have h : ((childLL thetaAboveCell000023112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112130) h)
        (by
          have h : ((childLH thetaAboveCell000023112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112130) h)
        (by
          have h : ((childHL thetaAboveCell000023112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112130) h)
        (by
          have h : ((childHH thetaAboveCell000023112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112131
        (by
          have h : ((childLL thetaAboveCell000023112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112131) h)
        (by
          have h : ((childLH thetaAboveCell000023112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112131) h)
        (by
          have h : ((childHL thetaAboveCell000023112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112131) h)
        (by
          have h : ((childHH thetaAboveCell000023112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112131) h))
    (by
      have h : (thetaAboveCell000023112132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112132 h)
    (by
      have h : (thetaAboveCell000023112133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112133 h)

theorem e24KC2ThetaAboveLeaf0000231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002311))
    cover_subtree_be8b495598ef
    cover_subtree_b9cce4a71b20
    cover_subtree_f376dd8d0235
    cover_subtree_a9dfb54a5534
theorem e24KC2ThetaAboveLeaf0000231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002311))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002311))) h)
theorem e24KC2ThetaAboveLeaf0000231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002311))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002311))) h)
theorem cover_subtree_d1cb21971feb :
    adaptiveCoverCheck 7 thetaAboveCell000023113002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113002)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113002)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113002)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023113002)
        (by
          have h : ((childLL (childHH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023113002)) h))

theorem cover_subtree_3efb79a6f9e0 :
    adaptiveCoverCheck 7 thetaAboveCell000023113003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113003)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113003)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113003)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023113003)
        (by
          have h : ((childLL (childHH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023113003)) h))

theorem cover_subtree_f6e1fff83561 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113000
        (by
          have h : ((childLL thetaAboveCell000023113000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113000) h)
        (by
          have h : ((childLH thetaAboveCell000023113000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113000) h)
        (by
          have h : ((childHL thetaAboveCell000023113000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113000) h)
        (by
          have h : ((childHH thetaAboveCell000023113000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113001
        (by
          have h : ((childLL thetaAboveCell000023113001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113001) h)
        (by
          have h : ((childLH thetaAboveCell000023113001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113001) h)
        (by
          have h : ((childHL thetaAboveCell000023113001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113001) h)
        (by
          have h : ((childHH thetaAboveCell000023113001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113001) h))
    cover_subtree_d1cb21971feb
    cover_subtree_3efb79a6f9e0

theorem cover_subtree_4cb56c792c1b :
    adaptiveCoverCheck 7 thetaAboveCell000023113012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113012)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113012)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113012)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023113012)
        (by
          have h : ((childLL (childHH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023113012)) h))

theorem cover_subtree_d84633da1a8a :
    adaptiveCoverCheck 7 thetaAboveCell000023113013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113013)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113013)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113013)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023113013)
        (by
          have h : ((childLL (childHH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023113013)) h))

theorem cover_subtree_5c601c4361a5 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113010
        (by
          have h : ((childLL thetaAboveCell000023113010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113010) h)
        (by
          have h : ((childLH thetaAboveCell000023113010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113010) h)
        (by
          have h : ((childHL thetaAboveCell000023113010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113010) h)
        (by
          have h : ((childHH thetaAboveCell000023113010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113011
        (by
          have h : ((childLL thetaAboveCell000023113011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113011) h)
        (by
          have h : ((childLH thetaAboveCell000023113011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113011) h)
        (by
          have h : ((childHL thetaAboveCell000023113011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113011) h)
        (by
          have h : ((childHH thetaAboveCell000023113011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113011) h))
    cover_subtree_4cb56c792c1b
    cover_subtree_d84633da1a8a

theorem cover_subtree_7c8020e781ad :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113020
        (by
          have h : ((childLL thetaAboveCell000023113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113020) h)
        (by
          have h : ((childLH thetaAboveCell000023113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113020) h)
        (by
          have h : ((childHL thetaAboveCell000023113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113020) h)
        (by
          have h : ((childHH thetaAboveCell000023113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113021
        (by
          have h : ((childLL thetaAboveCell000023113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113021) h)
        (by
          have h : ((childLH thetaAboveCell000023113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113021) h)
        (by
          have h : ((childHL thetaAboveCell000023113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113021) h)
        (by
          have h : ((childHH thetaAboveCell000023113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113021) h))
    (by
      have h : (thetaAboveCell000023113022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113022 h)
    (by
      have h : (thetaAboveCell000023113023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113023 h)

theorem cover_subtree_01c951b510fe :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113030
        (by
          have h : ((childLL thetaAboveCell000023113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113030) h)
        (by
          have h : ((childLH thetaAboveCell000023113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113030) h)
        (by
          have h : ((childHL thetaAboveCell000023113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113030) h)
        (by
          have h : ((childHH thetaAboveCell000023113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113031
        (by
          have h : ((childLL thetaAboveCell000023113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113031) h)
        (by
          have h : ((childLH thetaAboveCell000023113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113031) h)
        (by
          have h : ((childHL thetaAboveCell000023113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113031) h)
        (by
          have h : ((childHH thetaAboveCell000023113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113031) h))
    (by
      have h : (thetaAboveCell000023113032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113032 h)
    (by
      have h : (thetaAboveCell000023113033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113033 h)

theorem e24KC2ThetaAboveLeaf0000231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002311))
    cover_subtree_f6e1fff83561
    cover_subtree_5c601c4361a5
    cover_subtree_7c8020e781ad
    cover_subtree_01c951b510fe
theorem cover_subtree_195c372ae99b :
    adaptiveCoverCheck 7 thetaAboveCell000023113102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113102)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113102)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113102)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113102)) h))
    (by
      have h : ((childHH thetaAboveCell000023113102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113102) h)

theorem cover_subtree_d1cce1dbdb65 :
    adaptiveCoverCheck 7 thetaAboveCell000023113103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113103)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113103)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113103)) h))
    (by
      have h : ((childHL thetaAboveCell000023113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113103) h)
    (by
      have h : ((childHH thetaAboveCell000023113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113103) h)

theorem cover_subtree_f77ed6807865 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113100
        (by
          have h : ((childLL thetaAboveCell000023113100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113100) h)
        (by
          have h : ((childLH thetaAboveCell000023113100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113100) h)
        (by
          have h : ((childHL thetaAboveCell000023113100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113100) h)
        (by
          have h : ((childHH thetaAboveCell000023113100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113101
        (by
          have h : ((childLL thetaAboveCell000023113101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113101) h)
        (by
          have h : ((childLH thetaAboveCell000023113101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113101) h)
        (by
          have h : ((childHL thetaAboveCell000023113101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113101) h)
        (by
          have h : ((childHH thetaAboveCell000023113101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113101) h))
    cover_subtree_195c372ae99b
    cover_subtree_d1cce1dbdb65

theorem cover_subtree_93cb889e1841 :
    adaptiveCoverCheck 7 thetaAboveCell000023113112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113112)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113112)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113112)) h))
    (by
      have h : ((childHL thetaAboveCell000023113112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113112) h)
    (by
      have h : ((childHH thetaAboveCell000023113112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113112) h)

theorem cover_subtree_dd2e8b0050d0 :
    adaptiveCoverCheck 7 thetaAboveCell000023113113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113113)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113113)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113113)) h))
    (by
      have h : ((childHL thetaAboveCell000023113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113113) h)
    (by
      have h : ((childHH thetaAboveCell000023113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113113) h)

theorem cover_subtree_9bd401d941dd :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113110
        (by
          have h : ((childLL thetaAboveCell000023113110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113110) h)
        (by
          have h : ((childLH thetaAboveCell000023113110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113110) h)
        (by
          have h : ((childHL thetaAboveCell000023113110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113110) h)
        (by
          have h : ((childHH thetaAboveCell000023113110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113111
        (by
          have h : ((childLL thetaAboveCell000023113111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113111) h)
        (by
          have h : ((childLH thetaAboveCell000023113111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113111) h)
        (by
          have h : ((childHL thetaAboveCell000023113111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113111) h)
        (by
          have h : ((childHH thetaAboveCell000023113111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113111) h))
    cover_subtree_93cb889e1841
    cover_subtree_dd2e8b0050d0

theorem cover_subtree_17ce5f0eb4e5 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113120
        (by
          have h : ((childLL thetaAboveCell000023113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113120) h)
        (by
          have h : ((childLH thetaAboveCell000023113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113120) h)
        (by
          have h : ((childHL thetaAboveCell000023113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113120) h)
        (by
          have h : ((childHH thetaAboveCell000023113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113121
        (by
          have h : ((childLL thetaAboveCell000023113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113121) h)
        (by
          have h : ((childLH thetaAboveCell000023113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113121) h)
        (by
          have h : ((childHL thetaAboveCell000023113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113121) h)
        (by
          have h : ((childHH thetaAboveCell000023113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113121) h))
    (by
      have h : (thetaAboveCell000023113122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113122 h)
    (by
      have h : (thetaAboveCell000023113123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113123 h)

theorem cover_subtree_167fbbc5bd30 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113130
        (by
          have h : ((childLL thetaAboveCell000023113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113130) h)
        (by
          have h : ((childLH thetaAboveCell000023113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113130) h)
        (by
          have h : ((childHL thetaAboveCell000023113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113130) h)
        (by
          have h : ((childHH thetaAboveCell000023113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113131
        (by
          have h : ((childLL thetaAboveCell000023113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113131) h)
        (by
          have h : ((childLH thetaAboveCell000023113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113131) h)
        (by
          have h : ((childHL thetaAboveCell000023113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113131) h)
        (by
          have h : ((childHH thetaAboveCell000023113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113131) h))
    (by
      have h : (thetaAboveCell000023113132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113132 h)
    (by
      have h : (thetaAboveCell000023113133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113133 h)

theorem e24KC2ThetaAboveLeaf0000231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002311))
    cover_subtree_f77ed6807865
    cover_subtree_9bd401d941dd
    cover_subtree_17ce5f0eb4e5
    cover_subtree_167fbbc5bd30
theorem e24KC2ThetaAboveLeaf0000231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002311))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002311))) h)
theorem e24KC2ThetaAboveLeaf0000231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002311))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002311))) h)
theorem e24KC2ThetaAboveLeaf0000320002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003200))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032000220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000220 h)
        (by
          have h : (thetaAboveCell000032000221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000221 h)
        (by
          have h : (thetaAboveCell000032000222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000222 h)
        (by
          have h : (thetaAboveCell000032000223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032000230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000230 h)
        (by
          have h : (thetaAboveCell000032000231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000231 h)
        (by
          have h : (thetaAboveCell000032000232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000232 h)
        (by
          have h : (thetaAboveCell000032000233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000233 h))
theorem e24KC2ThetaAboveLeaf0000320003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003200))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032000320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000320 h)
        (by
          have h : (thetaAboveCell000032000321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000321 h)
        (by
          have h : (thetaAboveCell000032000322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000322 h)
        (by
          have h : (thetaAboveCell000032000323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032000330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000330 h)
        (by
          have h : (thetaAboveCell000032000331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000331 h)
        (by
          have h : (thetaAboveCell000032000332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000332 h)
        (by
          have h : (thetaAboveCell000032000333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000333 h))
theorem e24KC2ThetaAboveLeaf0000320012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003200))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032001220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032001220 h)
        (by
          have h : (thetaAboveCell000032001221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032001221 h)
        (by
          have h : (thetaAboveCell000032001222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032001222 h)
        (by
          have h : (thetaAboveCell000032001223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032001223 h))
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003200))) h)
theorem e24KC2ThetaAboveLeaf0000320013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003200))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003200))) h)
theorem cover_subtree_dc923db2d444 :
    adaptiveCoverCheck 7 thetaAboveCell000032002002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000032002002)
        (by
          have h : ((childLL (childLL thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000032002002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000032002002)
        (by
          have h : ((childLL (childLH thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000032002002)) h))
    (by
      have h : ((childHL thetaAboveCell000032002002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002002) h)
    (by
      have h : ((childHH thetaAboveCell000032002002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002002) h)

theorem cover_subtree_3d16a69d20d7 :
    adaptiveCoverCheck 7 thetaAboveCell000032002003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000032002003)
        (by
          have h : ((childLL (childLL thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000032002003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000032002003)
        (by
          have h : ((childLL (childLH thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000032002003)) h))
    (by
      have h : ((childHL thetaAboveCell000032002003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002003) h)
    (by
      have h : ((childHH thetaAboveCell000032002003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002003) h)

theorem cover_subtree_80a354cc93c8 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002000
        (by
          have h : ((childLL thetaAboveCell000032002000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002000) h)
        (by
          have h : ((childLH thetaAboveCell000032002000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002000) h)
        (by
          have h : ((childHL thetaAboveCell000032002000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002000) h)
        (by
          have h : ((childHH thetaAboveCell000032002000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002001
        (by
          have h : ((childLL thetaAboveCell000032002001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002001) h)
        (by
          have h : ((childLH thetaAboveCell000032002001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002001) h)
        (by
          have h : ((childHL thetaAboveCell000032002001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002001) h)
        (by
          have h : ((childHH thetaAboveCell000032002001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002001) h))
    cover_subtree_dc923db2d444
    cover_subtree_3d16a69d20d7

theorem cover_subtree_0a679df94e2d :
    adaptiveCoverCheck 7 thetaAboveCell000032002012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000032002012)
        (by
          have h : ((childLL (childLL thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000032002012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000032002012)
        (by
          have h : ((childLL (childLH thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000032002012)) h))
    (by
      have h : ((childHL thetaAboveCell000032002012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002012) h)
    (by
      have h : ((childHH thetaAboveCell000032002012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002012) h)

theorem cover_subtree_a9518d4839ee :
    adaptiveCoverCheck 7 thetaAboveCell000032002013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000032002013)
        (by
          have h : ((childLL (childLL thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000032002013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000032002013)
        (by
          have h : ((childLL (childLH thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000032002013)) h))
    (by
      have h : ((childHL thetaAboveCell000032002013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002013) h)
    (by
      have h : ((childHH thetaAboveCell000032002013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002013) h)

theorem cover_subtree_69eb32740a9f :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002010
        (by
          have h : ((childLL thetaAboveCell000032002010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002010) h)
        (by
          have h : ((childLH thetaAboveCell000032002010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002010) h)
        (by
          have h : ((childHL thetaAboveCell000032002010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002010) h)
        (by
          have h : ((childHH thetaAboveCell000032002010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002011
        (by
          have h : ((childLL thetaAboveCell000032002011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002011) h)
        (by
          have h : ((childLH thetaAboveCell000032002011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002011) h)
        (by
          have h : ((childHL thetaAboveCell000032002011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002011) h)
        (by
          have h : ((childHH thetaAboveCell000032002011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002011) h))
    cover_subtree_0a679df94e2d
    cover_subtree_a9518d4839ee

theorem cover_subtree_0afe6e641e2b :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002020
        (by
          have h : ((childLL thetaAboveCell000032002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002020) h)
        (by
          have h : ((childLH thetaAboveCell000032002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002020) h)
        (by
          have h : ((childHL thetaAboveCell000032002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002020) h)
        (by
          have h : ((childHH thetaAboveCell000032002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002021
        (by
          have h : ((childLL thetaAboveCell000032002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002021) h)
        (by
          have h : ((childLH thetaAboveCell000032002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002021) h)
        (by
          have h : ((childHL thetaAboveCell000032002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002021) h)
        (by
          have h : ((childHH thetaAboveCell000032002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002021) h))
    (by
      have h : (thetaAboveCell000032002022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002022 h)
    (by
      have h : (thetaAboveCell000032002023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002023 h)

theorem cover_subtree_13f8c37ba985 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002030
        (by
          have h : ((childLL thetaAboveCell000032002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002030) h)
        (by
          have h : ((childLH thetaAboveCell000032002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002030) h)
        (by
          have h : ((childHL thetaAboveCell000032002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002030) h)
        (by
          have h : ((childHH thetaAboveCell000032002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002031
        (by
          have h : ((childLL thetaAboveCell000032002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002031) h)
        (by
          have h : ((childLH thetaAboveCell000032002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002031) h)
        (by
          have h : ((childHL thetaAboveCell000032002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002031) h)
        (by
          have h : ((childHH thetaAboveCell000032002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002031) h))
    (by
      have h : (thetaAboveCell000032002032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002032 h)
    (by
      have h : (thetaAboveCell000032002033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002033 h)

theorem e24KC2ThetaAboveLeaf0000320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003200))
    cover_subtree_80a354cc93c8
    cover_subtree_69eb32740a9f
    cover_subtree_0afe6e641e2b
    cover_subtree_13f8c37ba985
theorem cover_subtree_6185ee76a9ce :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002100
        (by
          have h : ((childLL thetaAboveCell000032002100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002100) h)
        (by
          have h : ((childLH thetaAboveCell000032002100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002100) h)
        (by
          have h : ((childHL thetaAboveCell000032002100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002100) h)
        (by
          have h : ((childHH thetaAboveCell000032002100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002101
        (by
          have h : ((childLL thetaAboveCell000032002101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002101) h)
        (by
          have h : ((childLH thetaAboveCell000032002101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002101) h)
        (by
          have h : ((childHL thetaAboveCell000032002101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002101) h)
        (by
          have h : ((childHH thetaAboveCell000032002101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002101) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002102
        (by
          have h : ((childLL thetaAboveCell000032002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002102) h)
        (by
          have h : ((childLH thetaAboveCell000032002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002102) h)
        (by
          have h : ((childHL thetaAboveCell000032002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002102) h)
        (by
          have h : ((childHH thetaAboveCell000032002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002103
        (by
          have h : ((childLL thetaAboveCell000032002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002103) h)
        (by
          have h : ((childLH thetaAboveCell000032002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002103) h)
        (by
          have h : ((childHL thetaAboveCell000032002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002103) h)
        (by
          have h : ((childHH thetaAboveCell000032002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002103) h))

theorem cover_subtree_d6e21884e5c8 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002110
        (by
          have h : ((childLL thetaAboveCell000032002110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002110) h)
        (by
          have h : ((childLH thetaAboveCell000032002110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002110) h)
        (by
          have h : ((childHL thetaAboveCell000032002110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002110) h)
        (by
          have h : ((childHH thetaAboveCell000032002110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002111
        (by
          have h : ((childLL thetaAboveCell000032002111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002111) h)
        (by
          have h : ((childLH thetaAboveCell000032002111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002111) h)
        (by
          have h : ((childHL thetaAboveCell000032002111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002111) h)
        (by
          have h : ((childHH thetaAboveCell000032002111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002111) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002112
        (by
          have h : ((childLL thetaAboveCell000032002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002112) h)
        (by
          have h : ((childLH thetaAboveCell000032002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002112) h)
        (by
          have h : ((childHL thetaAboveCell000032002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002112) h)
        (by
          have h : ((childHH thetaAboveCell000032002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002113
        (by
          have h : ((childLL thetaAboveCell000032002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002113) h)
        (by
          have h : ((childLH thetaAboveCell000032002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002113) h)
        (by
          have h : ((childHL thetaAboveCell000032002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002113) h)
        (by
          have h : ((childHH thetaAboveCell000032002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002113) h))

theorem cover_subtree_d4ae0081215d :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002120
        (by
          have h : ((childLL thetaAboveCell000032002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002120) h)
        (by
          have h : ((childLH thetaAboveCell000032002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002120) h)
        (by
          have h : ((childHL thetaAboveCell000032002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002120) h)
        (by
          have h : ((childHH thetaAboveCell000032002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002121
        (by
          have h : ((childLL thetaAboveCell000032002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002121) h)
        (by
          have h : ((childLH thetaAboveCell000032002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002121) h)
        (by
          have h : ((childHL thetaAboveCell000032002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002121) h)
        (by
          have h : ((childHH thetaAboveCell000032002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002121) h))
    (by
      have h : (thetaAboveCell000032002122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002122 h)
    (by
      have h : (thetaAboveCell000032002123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002123 h)

theorem cover_subtree_14b21c11f4bb :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002130
        (by
          have h : ((childLL thetaAboveCell000032002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002130) h)
        (by
          have h : ((childLH thetaAboveCell000032002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002130) h)
        (by
          have h : ((childHL thetaAboveCell000032002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002130) h)
        (by
          have h : ((childHH thetaAboveCell000032002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002131
        (by
          have h : ((childLL thetaAboveCell000032002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002131) h)
        (by
          have h : ((childLH thetaAboveCell000032002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002131) h)
        (by
          have h : ((childHL thetaAboveCell000032002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002131) h)
        (by
          have h : ((childHH thetaAboveCell000032002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002131) h))
    (by
      have h : (thetaAboveCell000032002132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002132 h)
    (by
      have h : (thetaAboveCell000032002133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002133 h)

theorem e24KC2ThetaAboveLeaf0000320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003200))
    cover_subtree_6185ee76a9ce
    cover_subtree_d6e21884e5c8
    cover_subtree_d4ae0081215d
    cover_subtree_14b21c11f4bb
theorem e24KC2ThetaAboveLeaf0000320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003200))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003200))) h)
theorem e24KC2ThetaAboveLeaf0000320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003200))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003200))) h)
theorem cover_subtree_0c3f9f5d2a22 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003000
        (by
          have h : ((childLL thetaAboveCell000032003000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003000) h)
        (by
          have h : ((childLH thetaAboveCell000032003000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003000) h)
        (by
          have h : ((childHL thetaAboveCell000032003000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003000) h)
        (by
          have h : ((childHH thetaAboveCell000032003000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003001
        (by
          have h : ((childLL thetaAboveCell000032003001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003001) h)
        (by
          have h : ((childLH thetaAboveCell000032003001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003001) h)
        (by
          have h : ((childHL thetaAboveCell000032003001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003001) h)
        (by
          have h : ((childHH thetaAboveCell000032003001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003001) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003002
        (by
          have h : ((childLL thetaAboveCell000032003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003002) h)
        (by
          have h : ((childLH thetaAboveCell000032003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003002) h)
        (by
          have h : ((childHL thetaAboveCell000032003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003002) h)
        (by
          have h : ((childHH thetaAboveCell000032003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003003
        (by
          have h : ((childLL thetaAboveCell000032003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003003) h)
        (by
          have h : ((childLH thetaAboveCell000032003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003003) h)
        (by
          have h : ((childHL thetaAboveCell000032003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003003) h)
        (by
          have h : ((childHH thetaAboveCell000032003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003003) h))

theorem cover_subtree_e68bbaf0142c :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003010
        (by
          have h : ((childLL thetaAboveCell000032003010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003010) h)
        (by
          have h : ((childLH thetaAboveCell000032003010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003010) h)
        (by
          have h : ((childHL thetaAboveCell000032003010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003010) h)
        (by
          have h : ((childHH thetaAboveCell000032003010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003011
        (by
          have h : ((childLL thetaAboveCell000032003011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003011) h)
        (by
          have h : ((childLH thetaAboveCell000032003011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003011) h)
        (by
          have h : ((childHL thetaAboveCell000032003011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003011) h)
        (by
          have h : ((childHH thetaAboveCell000032003011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003011) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003012
        (by
          have h : ((childLL thetaAboveCell000032003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003012) h)
        (by
          have h : ((childLH thetaAboveCell000032003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003012) h)
        (by
          have h : ((childHL thetaAboveCell000032003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003012) h)
        (by
          have h : ((childHH thetaAboveCell000032003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003013
        (by
          have h : ((childLL thetaAboveCell000032003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003013) h)
        (by
          have h : ((childLH thetaAboveCell000032003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003013) h)
        (by
          have h : ((childHL thetaAboveCell000032003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003013) h)
        (by
          have h : ((childHH thetaAboveCell000032003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003013) h))

theorem cover_subtree_80b59cc08427 :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003020
        (by
          have h : ((childLL thetaAboveCell000032003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003020) h)
        (by
          have h : ((childLH thetaAboveCell000032003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003020) h)
        (by
          have h : ((childHL thetaAboveCell000032003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003020) h)
        (by
          have h : ((childHH thetaAboveCell000032003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003021
        (by
          have h : ((childLL thetaAboveCell000032003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003021) h)
        (by
          have h : ((childLH thetaAboveCell000032003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003021) h)
        (by
          have h : ((childHL thetaAboveCell000032003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003021) h)
        (by
          have h : ((childHH thetaAboveCell000032003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003021) h))
    (by
      have h : (thetaAboveCell000032003022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003022 h)
    (by
      have h : (thetaAboveCell000032003023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003023 h)

theorem cover_subtree_45a4c3e7665d :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003030
        (by
          have h : ((childLL thetaAboveCell000032003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003030) h)
        (by
          have h : ((childLH thetaAboveCell000032003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003030) h)
        (by
          have h : ((childHL thetaAboveCell000032003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003030) h)
        (by
          have h : ((childHH thetaAboveCell000032003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003031
        (by
          have h : ((childLL thetaAboveCell000032003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003031) h)
        (by
          have h : ((childLH thetaAboveCell000032003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003031) h)
        (by
          have h : ((childHL thetaAboveCell000032003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003031) h)
        (by
          have h : ((childHH thetaAboveCell000032003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003031) h))
    (by
      have h : (thetaAboveCell000032003032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003032 h)
    (by
      have h : (thetaAboveCell000032003033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003033 h)

theorem e24KC2ThetaAboveLeaf0000320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003200))
    cover_subtree_0c3f9f5d2a22
    cover_subtree_e68bbaf0142c
    cover_subtree_80b59cc08427
    cover_subtree_45a4c3e7665d
theorem cover_subtree_cabec6ebeaec :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003100
        (by
          have h : ((childLL thetaAboveCell000032003100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003100) h)
        (by
          have h : ((childLH thetaAboveCell000032003100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003100) h)
        (by
          have h : ((childHL thetaAboveCell000032003100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003100) h)
        (by
          have h : ((childHH thetaAboveCell000032003100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003101
        (by
          have h : ((childLL thetaAboveCell000032003101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003101) h)
        (by
          have h : ((childLH thetaAboveCell000032003101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003101) h)
        (by
          have h : ((childHL thetaAboveCell000032003101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003101) h)
        (by
          have h : ((childHH thetaAboveCell000032003101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003101) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003102
        (by
          have h : ((childLL thetaAboveCell000032003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003102) h)
        (by
          have h : ((childLH thetaAboveCell000032003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003102) h)
        (by
          have h : ((childHL thetaAboveCell000032003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003102) h)
        (by
          have h : ((childHH thetaAboveCell000032003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003103
        (by
          have h : ((childLL thetaAboveCell000032003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003103) h)
        (by
          have h : ((childLH thetaAboveCell000032003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003103) h)
        (by
          have h : ((childHL thetaAboveCell000032003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003103) h)
        (by
          have h : ((childHH thetaAboveCell000032003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003103) h))

theorem cover_subtree_f94fc5a27c16 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003110
        (by
          have h : ((childLL thetaAboveCell000032003110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003110) h)
        (by
          have h : ((childLH thetaAboveCell000032003110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003110) h)
        (by
          have h : ((childHL thetaAboveCell000032003110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003110) h)
        (by
          have h : ((childHH thetaAboveCell000032003110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003111
        (by
          have h : ((childLL thetaAboveCell000032003111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003111) h)
        (by
          have h : ((childLH thetaAboveCell000032003111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003111) h)
        (by
          have h : ((childHL thetaAboveCell000032003111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003111) h)
        (by
          have h : ((childHH thetaAboveCell000032003111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003111) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003112
        (by
          have h : ((childLL thetaAboveCell000032003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003112) h)
        (by
          have h : ((childLH thetaAboveCell000032003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003112) h)
        (by
          have h : ((childHL thetaAboveCell000032003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003112) h)
        (by
          have h : ((childHH thetaAboveCell000032003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003113
        (by
          have h : ((childLL thetaAboveCell000032003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003113) h)
        (by
          have h : ((childLH thetaAboveCell000032003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003113) h)
        (by
          have h : ((childHL thetaAboveCell000032003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003113) h)
        (by
          have h : ((childHH thetaAboveCell000032003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003113) h))

theorem cover_subtree_5a58662c5bc0 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003120
        (by
          have h : ((childLL thetaAboveCell000032003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003120) h)
        (by
          have h : ((childLH thetaAboveCell000032003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003120) h)
        (by
          have h : ((childHL thetaAboveCell000032003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003120) h)
        (by
          have h : ((childHH thetaAboveCell000032003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003121
        (by
          have h : ((childLL thetaAboveCell000032003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003121) h)
        (by
          have h : ((childLH thetaAboveCell000032003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003121) h)
        (by
          have h : ((childHL thetaAboveCell000032003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003121) h)
        (by
          have h : ((childHH thetaAboveCell000032003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003121) h))
    (by
      have h : (thetaAboveCell000032003122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003122 h)
    (by
      have h : (thetaAboveCell000032003123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003123 h)

theorem cover_subtree_38aaf5d7c82e :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003130
        (by
          have h : ((childLL thetaAboveCell000032003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003130) h)
        (by
          have h : ((childLH thetaAboveCell000032003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003130) h)
        (by
          have h : ((childHL thetaAboveCell000032003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003130) h)
        (by
          have h : ((childHH thetaAboveCell000032003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003131
        (by
          have h : ((childLL thetaAboveCell000032003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003131) h)
        (by
          have h : ((childLH thetaAboveCell000032003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003131) h)
        (by
          have h : ((childHL thetaAboveCell000032003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003131) h)
        (by
          have h : ((childHH thetaAboveCell000032003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003131) h))
    (by
      have h : (thetaAboveCell000032003132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003132 h)
    (by
      have h : (thetaAboveCell000032003133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003133 h)

theorem e24KC2ThetaAboveLeaf0000320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003200))
    cover_subtree_cabec6ebeaec
    cover_subtree_f94fc5a27c16
    cover_subtree_5a58662c5bc0
    cover_subtree_38aaf5d7c82e
theorem e24KC2ThetaAboveLeaf0000320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003200))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003200))) h)
theorem e24KC2ThetaAboveLeaf0000320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003200))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003200))) h)
theorem e24KC2ThetaAboveLeaf0000320102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003201))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003201))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003201))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003201))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003201))) h)

end PartE
end GerverSofa

end

end

end
