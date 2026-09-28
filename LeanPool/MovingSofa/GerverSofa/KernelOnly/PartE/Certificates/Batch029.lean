/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchDeeff549d6afce41`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC6 explicit proof-producing certificate batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7b7ba6d809

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0000)))
/-- Subcell `00003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0000)))
/-- Subcell `00003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0000)))
/-- Subcell `00003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0000)))
/-- Subcell `00003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0000)))
/-- Subcell `00003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0000)))
/-- Subcell `000032012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003201)))
/-- Subcell `000032012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003201)))
/-- Subcell `000032013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003201)))
/-- Subcell `000032013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003201)))
/-- Subcell `000032102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003210)))
/-- Subcell `000032102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003210)))
/-- Subcell `000032103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003210)))
/-- Subcell `000032103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003210)))
/-- Subcell `000032112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003211)))
/-- Subcell `000032112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003211)))
/-- Subcell `000032113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003211)))
/-- Subcell `000032113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000032113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003211)))
/-- Subcell `000033002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003300)))
/-- Subcell `000033002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003300)))
/-- Subcell `000033003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003300)))
/-- Subcell `000033003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003300)))
/-- Subcell `000033012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00003301)))
/-- Subcell `000033012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00003301)))
/-- Subcell `000033012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00003301)))
/-- Subcell `000033013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00003301)))
/-- Subcell `000033013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00003301)))
/-- Subcell `000033013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00003301)))
/-- Subcell `000033102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003310)))
/-- Subcell `000033102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003310)))

end CertificateCells7b7ba6d809

open CertificateCells7b7ba6d809
theorem cover_subtree_7c323abdd313 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012000
        (by
          have h : ((childLL thetaAboveCell000032012000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012000) h)
        (by
          have h : ((childLH thetaAboveCell000032012000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012000) h)
        (by
          have h : ((childHL thetaAboveCell000032012000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012000) h)
        (by
          have h : ((childHH thetaAboveCell000032012000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012001
        (by
          have h : ((childLL thetaAboveCell000032012001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012001) h)
        (by
          have h : ((childLH thetaAboveCell000032012001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012001) h)
        (by
          have h : ((childHL thetaAboveCell000032012001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012001) h)
        (by
          have h : ((childHH thetaAboveCell000032012001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012001) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012002
        (by
          have h : ((childLL thetaAboveCell000032012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012002) h)
        (by
          have h : ((childLH thetaAboveCell000032012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012002) h)
        (by
          have h : ((childHL thetaAboveCell000032012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012002) h)
        (by
          have h : ((childHH thetaAboveCell000032012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012003
        (by
          have h : ((childLL thetaAboveCell000032012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012003) h)
        (by
          have h : ((childLH thetaAboveCell000032012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012003) h)
        (by
          have h : ((childHL thetaAboveCell000032012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012003) h)
        (by
          have h : ((childHH thetaAboveCell000032012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012003) h))

theorem cover_subtree_2c6010c13cb7 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012010
        (by
          have h : ((childLL thetaAboveCell000032012010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012010) h)
        (by
          have h : ((childLH thetaAboveCell000032012010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012010) h)
        (by
          have h : ((childHL thetaAboveCell000032012010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012010) h)
        (by
          have h : ((childHH thetaAboveCell000032012010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012011
        (by
          have h : ((childLL thetaAboveCell000032012011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012011) h)
        (by
          have h : ((childLH thetaAboveCell000032012011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012011) h)
        (by
          have h : ((childHL thetaAboveCell000032012011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012011) h)
        (by
          have h : ((childHH thetaAboveCell000032012011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012011) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012012
        (by
          have h : ((childLL thetaAboveCell000032012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012012) h)
        (by
          have h : ((childLH thetaAboveCell000032012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012012) h)
        (by
          have h : ((childHL thetaAboveCell000032012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012012) h)
        (by
          have h : ((childHH thetaAboveCell000032012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012013
        (by
          have h : ((childLL thetaAboveCell000032012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012013) h)
        (by
          have h : ((childLH thetaAboveCell000032012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012013) h)
        (by
          have h : ((childHL thetaAboveCell000032012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012013) h)
        (by
          have h : ((childHH thetaAboveCell000032012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012013) h))

theorem cover_subtree_1c36f4e287e2 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012020
        (by
          have h : ((childLL thetaAboveCell000032012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012020) h)
        (by
          have h : ((childLH thetaAboveCell000032012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012020) h)
        (by
          have h : ((childHL thetaAboveCell000032012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012020) h)
        (by
          have h : ((childHH thetaAboveCell000032012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012021
        (by
          have h : ((childLL thetaAboveCell000032012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012021) h)
        (by
          have h : ((childLH thetaAboveCell000032012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012021) h)
        (by
          have h : ((childHL thetaAboveCell000032012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012021) h)
        (by
          have h : ((childHH thetaAboveCell000032012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012021) h))
    (by
      have h : (thetaAboveCell000032012022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012022 h)
    (by
      have h : (thetaAboveCell000032012023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012023 h)

theorem cover_subtree_2d88b84be921 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012030
        (by
          have h : ((childLL thetaAboveCell000032012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012030) h)
        (by
          have h : ((childLH thetaAboveCell000032012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012030) h)
        (by
          have h : ((childHL thetaAboveCell000032012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012030) h)
        (by
          have h : ((childHH thetaAboveCell000032012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012031
        (by
          have h : ((childLL thetaAboveCell000032012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012031) h)
        (by
          have h : ((childLH thetaAboveCell000032012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012031) h)
        (by
          have h : ((childHL thetaAboveCell000032012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012031) h)
        (by
          have h : ((childHH thetaAboveCell000032012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012031) h))
    (by
      have h : (thetaAboveCell000032012032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012032 h)
    (by
      have h : (thetaAboveCell000032012033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012033 h)

theorem e24KC2ThetaAboveLeaf0000320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003201))
    cover_subtree_7c323abdd313
    cover_subtree_2c6010c13cb7
    cover_subtree_1c36f4e287e2
    cover_subtree_2d88b84be921
theorem cover_subtree_15ce3b085062 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012100
        (by
          have h : ((childLL thetaAboveCell000032012100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012100) h)
        (by
          have h : ((childLH thetaAboveCell000032012100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012100) h)
        (by
          have h : ((childHL thetaAboveCell000032012100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012100) h)
        (by
          have h : ((childHH thetaAboveCell000032012100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012101
        (by
          have h : ((childLL thetaAboveCell000032012101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012101) h)
        (by
          have h : ((childLH thetaAboveCell000032012101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012101) h)
        (by
          have h : ((childHL thetaAboveCell000032012101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012101) h)
        (by
          have h : ((childHH thetaAboveCell000032012101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012101) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012102
        (by
          have h : ((childLL thetaAboveCell000032012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012102) h)
        (by
          have h : ((childLH thetaAboveCell000032012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012102) h)
        (by
          have h : ((childHL thetaAboveCell000032012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012102) h)
        (by
          have h : ((childHH thetaAboveCell000032012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012103
        (by
          have h : ((childLL thetaAboveCell000032012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012103) h)
        (by
          have h : ((childLH thetaAboveCell000032012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012103) h)
        (by
          have h : ((childHL thetaAboveCell000032012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012103) h)
        (by
          have h : ((childHH thetaAboveCell000032012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012103) h))

theorem cover_subtree_08caed552cac :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012110
        (by
          have h : ((childLL thetaAboveCell000032012110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012110) h)
        (by
          have h : ((childLH thetaAboveCell000032012110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012110) h)
        (by
          have h : ((childHL thetaAboveCell000032012110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012110) h)
        (by
          have h : ((childHH thetaAboveCell000032012110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012111
        (by
          have h : ((childLL thetaAboveCell000032012111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012111) h)
        (by
          have h : ((childLH thetaAboveCell000032012111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012111) h)
        (by
          have h : ((childHL thetaAboveCell000032012111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012111) h)
        (by
          have h : ((childHH thetaAboveCell000032012111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012111) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012112
        (by
          have h : ((childLL thetaAboveCell000032012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012112) h)
        (by
          have h : ((childLH thetaAboveCell000032012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012112) h)
        (by
          have h : ((childHL thetaAboveCell000032012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012112) h)
        (by
          have h : ((childHH thetaAboveCell000032012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012113
        (by
          have h : ((childLL thetaAboveCell000032012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012113) h)
        (by
          have h : ((childLH thetaAboveCell000032012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012113) h)
        (by
          have h : ((childHL thetaAboveCell000032012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012113) h)
        (by
          have h : ((childHH thetaAboveCell000032012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012113) h))

theorem cover_subtree_26481d0c715c :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012120
        (by
          have h : ((childLL thetaAboveCell000032012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012120) h)
        (by
          have h : ((childLH thetaAboveCell000032012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012120) h)
        (by
          have h : ((childHL thetaAboveCell000032012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012120) h)
        (by
          have h : ((childHH thetaAboveCell000032012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012121
        (by
          have h : ((childLL thetaAboveCell000032012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012121) h)
        (by
          have h : ((childLH thetaAboveCell000032012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012121) h)
        (by
          have h : ((childHL thetaAboveCell000032012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012121) h)
        (by
          have h : ((childHH thetaAboveCell000032012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012121) h))
    (by
      have h : (thetaAboveCell000032012122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012122 h)
    (by
      have h : (thetaAboveCell000032012123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012123 h)

theorem cover_subtree_a0f2894108e0 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012130
        (by
          have h : ((childLL thetaAboveCell000032012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012130) h)
        (by
          have h : ((childLH thetaAboveCell000032012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012130) h)
        (by
          have h : ((childHL thetaAboveCell000032012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012130) h)
        (by
          have h : ((childHH thetaAboveCell000032012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012131
        (by
          have h : ((childLL thetaAboveCell000032012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012131) h)
        (by
          have h : ((childLH thetaAboveCell000032012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012131) h)
        (by
          have h : ((childHL thetaAboveCell000032012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012131) h)
        (by
          have h : ((childHH thetaAboveCell000032012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012131) h))
    (by
      have h : (thetaAboveCell000032012132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012132 h)
    (by
      have h : (thetaAboveCell000032012133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012133 h)

theorem e24KC2ThetaAboveLeaf0000320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003201))
    cover_subtree_15ce3b085062
    cover_subtree_08caed552cac
    cover_subtree_26481d0c715c
    cover_subtree_a0f2894108e0
theorem e24KC2ThetaAboveLeaf0000320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003201))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003201))) h)
theorem cover_subtree_69db60e02bff :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013000
        (by
          have h : ((childLL thetaAboveCell000032013000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013000) h)
        (by
          have h : ((childLH thetaAboveCell000032013000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013000) h)
        (by
          have h : ((childHL thetaAboveCell000032013000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013000) h)
        (by
          have h : ((childHH thetaAboveCell000032013000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013001
        (by
          have h : ((childLL thetaAboveCell000032013001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013001) h)
        (by
          have h : ((childLH thetaAboveCell000032013001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013001) h)
        (by
          have h : ((childHL thetaAboveCell000032013001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013001) h)
        (by
          have h : ((childHH thetaAboveCell000032013001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013001) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013002
        (by
          have h : ((childLL thetaAboveCell000032013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013002) h)
        (by
          have h : ((childLH thetaAboveCell000032013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013002) h)
        (by
          have h : ((childHL thetaAboveCell000032013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013002) h)
        (by
          have h : ((childHH thetaAboveCell000032013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013003
        (by
          have h : ((childLL thetaAboveCell000032013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013003) h)
        (by
          have h : ((childLH thetaAboveCell000032013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013003) h)
        (by
          have h : ((childHL thetaAboveCell000032013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013003) h)
        (by
          have h : ((childHH thetaAboveCell000032013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013003) h))

theorem cover_subtree_42fb80f99488 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013010
        (by
          have h : ((childLL thetaAboveCell000032013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013010) h)
        (by
          have h : ((childLH thetaAboveCell000032013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013010) h)
        (by
          have h : ((childHL thetaAboveCell000032013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013010) h)
        (by
          have h : ((childHH thetaAboveCell000032013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013011
        (by
          have h : ((childLL thetaAboveCell000032013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013011) h)
        (by
          have h : ((childLH thetaAboveCell000032013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013011) h)
        (by
          have h : ((childHL thetaAboveCell000032013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013011) h)
        (by
          have h : ((childHH thetaAboveCell000032013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013011) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013012
        (by
          have h : ((childLL thetaAboveCell000032013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013012) h)
        (by
          have h : ((childLH thetaAboveCell000032013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013012) h)
        (by
          have h : ((childHL thetaAboveCell000032013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013012) h)
        (by
          have h : ((childHH thetaAboveCell000032013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013013
        (by
          have h : ((childLL thetaAboveCell000032013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013013) h)
        (by
          have h : ((childLH thetaAboveCell000032013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013013) h)
        (by
          have h : ((childHL thetaAboveCell000032013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013013) h)
        (by
          have h : ((childHH thetaAboveCell000032013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013013) h))

theorem cover_subtree_190c09664a4f :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013020
        (by
          have h : ((childLL thetaAboveCell000032013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013020) h)
        (by
          have h : ((childLH thetaAboveCell000032013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013020) h)
        (by
          have h : ((childHL thetaAboveCell000032013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013020) h)
        (by
          have h : ((childHH thetaAboveCell000032013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013021
        (by
          have h : ((childLL thetaAboveCell000032013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013021) h)
        (by
          have h : ((childLH thetaAboveCell000032013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013021) h)
        (by
          have h : ((childHL thetaAboveCell000032013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013021) h)
        (by
          have h : ((childHH thetaAboveCell000032013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013021) h))
    (by
      have h : (thetaAboveCell000032013022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013022 h)
    (by
      have h : (thetaAboveCell000032013023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013023 h)

theorem cover_subtree_f68e71dd24e5 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013030
        (by
          have h : ((childLL thetaAboveCell000032013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013030) h)
        (by
          have h : ((childLH thetaAboveCell000032013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013030) h)
        (by
          have h : ((childHL thetaAboveCell000032013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013030) h)
        (by
          have h : ((childHH thetaAboveCell000032013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013031
        (by
          have h : ((childLL thetaAboveCell000032013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013031) h)
        (by
          have h : ((childLH thetaAboveCell000032013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013031) h)
        (by
          have h : ((childHL thetaAboveCell000032013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013031) h)
        (by
          have h : ((childHH thetaAboveCell000032013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013031) h))
    (by
      have h : (thetaAboveCell000032013032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013032 h)
    (by
      have h : (thetaAboveCell000032013033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013033 h)

theorem e24KC2ThetaAboveLeaf0000320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003201))
    cover_subtree_69db60e02bff
    cover_subtree_42fb80f99488
    cover_subtree_190c09664a4f
    cover_subtree_f68e71dd24e5
theorem cover_subtree_7cb6ec704eae :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003201)))
    (by
      have h : (thetaAboveCell000032013100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013100 h)
    (by
      have h : (thetaAboveCell000032013101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013102
        (by
          have h : ((childLL thetaAboveCell000032013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013102) h)
        (by
          have h : ((childLH thetaAboveCell000032013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013102) h)
        (by
          have h : ((childHL thetaAboveCell000032013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013102) h)
        (by
          have h : ((childHH thetaAboveCell000032013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013103
        (by
          have h : ((childLL thetaAboveCell000032013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013103) h)
        (by
          have h : ((childLH thetaAboveCell000032013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013103) h)
        (by
          have h : ((childHL thetaAboveCell000032013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013103) h)
        (by
          have h : ((childHH thetaAboveCell000032013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013103) h))

theorem cover_subtree_5ed05ff39522 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003201)))
    (by
      have h : (thetaAboveCell000032013110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013110 h)
    (by
      have h : (thetaAboveCell000032013111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013112
        (by
          have h : ((childLL thetaAboveCell000032013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013112) h)
        (by
          have h : ((childLH thetaAboveCell000032013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013112) h)
        (by
          have h : ((childHL thetaAboveCell000032013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013112) h)
        (by
          have h : ((childHH thetaAboveCell000032013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013113
        (by
          have h : ((childLL thetaAboveCell000032013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013113) h)
        (by
          have h : ((childLH thetaAboveCell000032013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013113) h)
        (by
          have h : ((childHL thetaAboveCell000032013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013113) h)
        (by
          have h : ((childHH thetaAboveCell000032013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013113) h))

theorem cover_subtree_0c55724b42aa :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013120
        (by
          have h : ((childLL thetaAboveCell000032013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013120) h)
        (by
          have h : ((childLH thetaAboveCell000032013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013120) h)
        (by
          have h : ((childHL thetaAboveCell000032013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013120) h)
        (by
          have h : ((childHH thetaAboveCell000032013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013121
        (by
          have h : ((childLL thetaAboveCell000032013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013121) h)
        (by
          have h : ((childLH thetaAboveCell000032013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013121) h)
        (by
          have h : ((childHL thetaAboveCell000032013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013121) h)
        (by
          have h : ((childHH thetaAboveCell000032013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013121) h))
    (by
      have h : (thetaAboveCell000032013122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013122 h)
    (by
      have h : (thetaAboveCell000032013123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013123 h)

theorem cover_subtree_a20be064bbc9 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013130
        (by
          have h : ((childLL thetaAboveCell000032013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013130) h)
        (by
          have h : ((childLH thetaAboveCell000032013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013130) h)
        (by
          have h : ((childHL thetaAboveCell000032013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013130) h)
        (by
          have h : ((childHH thetaAboveCell000032013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013131
        (by
          have h : ((childLL thetaAboveCell000032013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013131) h)
        (by
          have h : ((childLH thetaAboveCell000032013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013131) h)
        (by
          have h : ((childHL thetaAboveCell000032013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013131) h)
        (by
          have h : ((childHH thetaAboveCell000032013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013131) h))
    (by
      have h : (thetaAboveCell000032013132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013132 h)
    (by
      have h : (thetaAboveCell000032013133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013133 h)

theorem e24KC2ThetaAboveLeaf0000320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003201))
    cover_subtree_7cb6ec704eae
    cover_subtree_5ed05ff39522
    cover_subtree_0c55724b42aa
    cover_subtree_a20be064bbc9
theorem e24KC2ThetaAboveLeaf0000320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000321002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003210))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003210))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003210))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003210))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003210))) h)
theorem cover_subtree_0ba391c6ec0d :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032102000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102000 h)
    (by
      have h : (thetaAboveCell000032102001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102002
        (by
          have h : ((childLL thetaAboveCell000032102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102002) h)
        (by
          have h : ((childLH thetaAboveCell000032102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102002) h)
        (by
          have h : ((childHL thetaAboveCell000032102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102002) h)
        (by
          have h : ((childHH thetaAboveCell000032102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102003
        (by
          have h : ((childLL thetaAboveCell000032102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102003) h)
        (by
          have h : ((childLH thetaAboveCell000032102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102003) h)
        (by
          have h : ((childHL thetaAboveCell000032102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102003) h)
        (by
          have h : ((childHH thetaAboveCell000032102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102003) h))

theorem cover_subtree_8fafa3f6224a :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032102010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102010 h)
    (by
      have h : (thetaAboveCell000032102011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102012
        (by
          have h : ((childLL thetaAboveCell000032102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102012) h)
        (by
          have h : ((childLH thetaAboveCell000032102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102012) h)
        (by
          have h : ((childHL thetaAboveCell000032102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102012) h)
        (by
          have h : ((childHH thetaAboveCell000032102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102013
        (by
          have h : ((childLL thetaAboveCell000032102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102013) h)
        (by
          have h : ((childLH thetaAboveCell000032102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102013) h)
        (by
          have h : ((childHL thetaAboveCell000032102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102013) h)
        (by
          have h : ((childHH thetaAboveCell000032102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102013) h))

theorem cover_subtree_d5e7f8726976 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102020
        (by
          have h : ((childLL thetaAboveCell000032102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102020) h)
        (by
          have h : ((childLH thetaAboveCell000032102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102020) h)
        (by
          have h : ((childHL thetaAboveCell000032102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102020) h)
        (by
          have h : ((childHH thetaAboveCell000032102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102021
        (by
          have h : ((childLL thetaAboveCell000032102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102021) h)
        (by
          have h : ((childLH thetaAboveCell000032102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102021) h)
        (by
          have h : ((childHL thetaAboveCell000032102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102021) h)
        (by
          have h : ((childHH thetaAboveCell000032102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102021) h))
    (by
      have h : (thetaAboveCell000032102022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102022 h)
    (by
      have h : (thetaAboveCell000032102023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102023 h)

theorem cover_subtree_c2e91aa19513 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102030
        (by
          have h : ((childLL thetaAboveCell000032102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102030) h)
        (by
          have h : ((childLH thetaAboveCell000032102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102030) h)
        (by
          have h : ((childHL thetaAboveCell000032102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102030) h)
        (by
          have h : ((childHH thetaAboveCell000032102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102031
        (by
          have h : ((childLL thetaAboveCell000032102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102031) h)
        (by
          have h : ((childLH thetaAboveCell000032102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102031) h)
        (by
          have h : ((childHL thetaAboveCell000032102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102031) h)
        (by
          have h : ((childHH thetaAboveCell000032102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102031) h))
    (by
      have h : (thetaAboveCell000032102032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102032 h)
    (by
      have h : (thetaAboveCell000032102033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102033 h)

theorem e24KC2ThetaAboveLeaf0000321020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003210))
    cover_subtree_0ba391c6ec0d
    cover_subtree_8fafa3f6224a
    cover_subtree_d5e7f8726976
    cover_subtree_c2e91aa19513
theorem cover_subtree_80cc442a7cb0 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032102100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102100 h)
    (by
      have h : (thetaAboveCell000032102101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102102
        (by
          have h : ((childLL thetaAboveCell000032102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102102) h)
        (by
          have h : ((childLH thetaAboveCell000032102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102102) h)
        (by
          have h : ((childHL thetaAboveCell000032102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102102) h)
        (by
          have h : ((childHH thetaAboveCell000032102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102103
        (by
          have h : ((childLL thetaAboveCell000032102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102103) h)
        (by
          have h : ((childLH thetaAboveCell000032102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102103) h)
        (by
          have h : ((childHL thetaAboveCell000032102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102103) h)
        (by
          have h : ((childHH thetaAboveCell000032102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102103) h))

theorem cover_subtree_7d2d9f5abf21 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032102110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102110 h)
    (by
      have h : (thetaAboveCell000032102111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102112
        (by
          have h : ((childLL thetaAboveCell000032102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102112) h)
        (by
          have h : ((childLH thetaAboveCell000032102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102112) h)
        (by
          have h : ((childHL thetaAboveCell000032102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102112) h)
        (by
          have h : ((childHH thetaAboveCell000032102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102113
        (by
          have h : ((childLL thetaAboveCell000032102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102113) h)
        (by
          have h : ((childLH thetaAboveCell000032102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102113) h)
        (by
          have h : ((childHL thetaAboveCell000032102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102113) h)
        (by
          have h : ((childHH thetaAboveCell000032102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102113) h))

theorem cover_subtree_4430ea3984ba :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102120
        (by
          have h : ((childLL thetaAboveCell000032102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102120) h)
        (by
          have h : ((childLH thetaAboveCell000032102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102120) h)
        (by
          have h : ((childHL thetaAboveCell000032102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102120) h)
        (by
          have h : ((childHH thetaAboveCell000032102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102121
        (by
          have h : ((childLL thetaAboveCell000032102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102121) h)
        (by
          have h : ((childLH thetaAboveCell000032102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102121) h)
        (by
          have h : ((childHL thetaAboveCell000032102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102121) h)
        (by
          have h : ((childHH thetaAboveCell000032102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102121) h))
    (by
      have h : (thetaAboveCell000032102122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102122 h)
    (by
      have h : (thetaAboveCell000032102123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102123 h)

theorem cover_subtree_7e0429da25bc :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102130
        (by
          have h : ((childLL thetaAboveCell000032102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102130) h)
        (by
          have h : ((childLH thetaAboveCell000032102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102130) h)
        (by
          have h : ((childHL thetaAboveCell000032102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102130) h)
        (by
          have h : ((childHH thetaAboveCell000032102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102131
        (by
          have h : ((childLL thetaAboveCell000032102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102131) h)
        (by
          have h : ((childLH thetaAboveCell000032102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102131) h)
        (by
          have h : ((childHL thetaAboveCell000032102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102131) h)
        (by
          have h : ((childHH thetaAboveCell000032102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102131) h))
    (by
      have h : (thetaAboveCell000032102132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102132 h)
    (by
      have h : (thetaAboveCell000032102133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102133 h)

theorem e24KC2ThetaAboveLeaf0000321021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003210))
    cover_subtree_80cc442a7cb0
    cover_subtree_7d2d9f5abf21
    cover_subtree_4430ea3984ba
    cover_subtree_7e0429da25bc
theorem e24KC2ThetaAboveLeaf0000321022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003210))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003210))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003210))) h)
theorem cover_subtree_c3fcf1053462 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032103000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103000 h)
    (by
      have h : (thetaAboveCell000032103001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103002
        (by
          have h : ((childLL thetaAboveCell000032103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103002) h)
        (by
          have h : ((childLH thetaAboveCell000032103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103002) h)
        (by
          have h : ((childHL thetaAboveCell000032103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103002) h)
        (by
          have h : ((childHH thetaAboveCell000032103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103003
        (by
          have h : ((childLL thetaAboveCell000032103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103003) h)
        (by
          have h : ((childLH thetaAboveCell000032103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103003) h)
        (by
          have h : ((childHL thetaAboveCell000032103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103003) h)
        (by
          have h : ((childHH thetaAboveCell000032103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103003) h))

theorem cover_subtree_c50e8ae52b0f :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032103010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103010 h)
    (by
      have h : (thetaAboveCell000032103011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103012
        (by
          have h : ((childLL thetaAboveCell000032103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103012) h)
        (by
          have h : ((childLH thetaAboveCell000032103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103012) h)
        (by
          have h : ((childHL thetaAboveCell000032103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103012) h)
        (by
          have h : ((childHH thetaAboveCell000032103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103013
        (by
          have h : ((childLL thetaAboveCell000032103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103013) h)
        (by
          have h : ((childLH thetaAboveCell000032103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103013) h)
        (by
          have h : ((childHL thetaAboveCell000032103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103013) h)
        (by
          have h : ((childHH thetaAboveCell000032103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103013) h))

theorem cover_subtree_d417fd422e6e :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103020
        (by
          have h : ((childLL thetaAboveCell000032103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103020) h)
        (by
          have h : ((childLH thetaAboveCell000032103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103020) h)
        (by
          have h : ((childHL thetaAboveCell000032103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103020) h)
        (by
          have h : ((childHH thetaAboveCell000032103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103021
        (by
          have h : ((childLL thetaAboveCell000032103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103021) h)
        (by
          have h : ((childLH thetaAboveCell000032103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103021) h)
        (by
          have h : ((childHL thetaAboveCell000032103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103021) h)
        (by
          have h : ((childHH thetaAboveCell000032103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103021) h))
    (by
      have h : (thetaAboveCell000032103022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103022 h)
    (by
      have h : (thetaAboveCell000032103023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103023 h)

theorem cover_subtree_803a1ba0f62b :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103030
        (by
          have h : ((childLL thetaAboveCell000032103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103030) h)
        (by
          have h : ((childLH thetaAboveCell000032103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103030) h)
        (by
          have h : ((childHL thetaAboveCell000032103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103030) h)
        (by
          have h : ((childHH thetaAboveCell000032103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103031
        (by
          have h : ((childLL thetaAboveCell000032103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103031) h)
        (by
          have h : ((childLH thetaAboveCell000032103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103031) h)
        (by
          have h : ((childHL thetaAboveCell000032103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103031) h)
        (by
          have h : ((childHH thetaAboveCell000032103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103031) h))
    (by
      have h : (thetaAboveCell000032103032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103032 h)
    (by
      have h : (thetaAboveCell000032103033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103033 h)

theorem e24KC2ThetaAboveLeaf0000321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003210))
    cover_subtree_c3fcf1053462
    cover_subtree_c50e8ae52b0f
    cover_subtree_d417fd422e6e
    cover_subtree_803a1ba0f62b
theorem cover_subtree_dc9cc0fd25e0 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032103100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103100 h)
    (by
      have h : (thetaAboveCell000032103101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103102
        (by
          have h : ((childLL thetaAboveCell000032103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103102) h)
        (by
          have h : ((childLH thetaAboveCell000032103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103102) h)
        (by
          have h : ((childHL thetaAboveCell000032103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103102) h)
        (by
          have h : ((childHH thetaAboveCell000032103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103103
        (by
          have h : ((childLL thetaAboveCell000032103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103103) h)
        (by
          have h : ((childLH thetaAboveCell000032103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103103) h)
        (by
          have h : ((childHL thetaAboveCell000032103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103103) h)
        (by
          have h : ((childHH thetaAboveCell000032103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103103) h))

theorem cover_subtree_4e80a706fe6e :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032103110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103110 h)
    (by
      have h : (thetaAboveCell000032103111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103112
        (by
          have h : ((childLL thetaAboveCell000032103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103112) h)
        (by
          have h : ((childLH thetaAboveCell000032103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103112) h)
        (by
          have h : ((childHL thetaAboveCell000032103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103112) h)
        (by
          have h : ((childHH thetaAboveCell000032103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103113
        (by
          have h : ((childLL thetaAboveCell000032103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103113) h)
        (by
          have h : ((childLH thetaAboveCell000032103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103113) h)
        (by
          have h : ((childHL thetaAboveCell000032103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103113) h)
        (by
          have h : ((childHH thetaAboveCell000032103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103113) h))

theorem cover_subtree_06156bdf5c57 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103120
        (by
          have h : ((childLL thetaAboveCell000032103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103120) h)
        (by
          have h : ((childLH thetaAboveCell000032103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103120) h)
        (by
          have h : ((childHL thetaAboveCell000032103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103120) h)
        (by
          have h : ((childHH thetaAboveCell000032103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103121
        (by
          have h : ((childLL thetaAboveCell000032103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103121) h)
        (by
          have h : ((childLH thetaAboveCell000032103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103121) h)
        (by
          have h : ((childHL thetaAboveCell000032103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103121) h)
        (by
          have h : ((childHH thetaAboveCell000032103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103121) h))
    (by
      have h : (thetaAboveCell000032103122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103122 h)
    (by
      have h : (thetaAboveCell000032103123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103123 h)

theorem cover_subtree_dfe1ff6f4f14 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103130
        (by
          have h : ((childLL thetaAboveCell000032103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103130) h)
        (by
          have h : ((childLH thetaAboveCell000032103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103130) h)
        (by
          have h : ((childHL thetaAboveCell000032103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103130) h)
        (by
          have h : ((childHH thetaAboveCell000032103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103131
        (by
          have h : ((childLL thetaAboveCell000032103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103131) h)
        (by
          have h : ((childLH thetaAboveCell000032103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103131) h)
        (by
          have h : ((childHL thetaAboveCell000032103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103131) h)
        (by
          have h : ((childHH thetaAboveCell000032103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103131) h))
    (by
      have h : (thetaAboveCell000032103132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103132 h)
    (by
      have h : (thetaAboveCell000032103133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103133 h)

theorem e24KC2ThetaAboveLeaf0000321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003210))
    cover_subtree_dc9cc0fd25e0
    cover_subtree_4e80a706fe6e
    cover_subtree_06156bdf5c57
    cover_subtree_dfe1ff6f4f14
theorem e24KC2ThetaAboveLeaf0000321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003211))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003211))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003211))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003211))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003211))) h)
theorem cover_subtree_5921e16da435 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032112000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112000 h)
    (by
      have h : (thetaAboveCell000032112001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112002
        (by
          have h : ((childLL thetaAboveCell000032112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112002) h)
        (by
          have h : ((childLH thetaAboveCell000032112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112002) h)
        (by
          have h : ((childHL thetaAboveCell000032112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112002) h)
        (by
          have h : ((childHH thetaAboveCell000032112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112003
        (by
          have h : ((childLL thetaAboveCell000032112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112003) h)
        (by
          have h : ((childLH thetaAboveCell000032112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112003) h)
        (by
          have h : ((childHL thetaAboveCell000032112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112003) h)
        (by
          have h : ((childHH thetaAboveCell000032112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112003) h))

theorem cover_subtree_52f1b09bd9bd :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032112010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112010 h)
    (by
      have h : (thetaAboveCell000032112011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112012
        (by
          have h : ((childLL thetaAboveCell000032112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112012) h)
        (by
          have h : ((childLH thetaAboveCell000032112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112012) h)
        (by
          have h : ((childHL thetaAboveCell000032112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112012) h)
        (by
          have h : ((childHH thetaAboveCell000032112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112013
        (by
          have h : ((childLL thetaAboveCell000032112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112013) h)
        (by
          have h : ((childLH thetaAboveCell000032112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112013) h)
        (by
          have h : ((childHL thetaAboveCell000032112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112013) h)
        (by
          have h : ((childHH thetaAboveCell000032112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112013) h))

theorem cover_subtree_0a1ef543bda5 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112020
        (by
          have h : ((childLL thetaAboveCell000032112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112020) h)
        (by
          have h : ((childLH thetaAboveCell000032112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112020) h)
        (by
          have h : ((childHL thetaAboveCell000032112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112020) h)
        (by
          have h : ((childHH thetaAboveCell000032112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112021
        (by
          have h : ((childLL thetaAboveCell000032112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112021) h)
        (by
          have h : ((childLH thetaAboveCell000032112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112021) h)
        (by
          have h : ((childHL thetaAboveCell000032112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112021) h)
        (by
          have h : ((childHH thetaAboveCell000032112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112021) h))
    (by
      have h : (thetaAboveCell000032112022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112022 h)
    (by
      have h : (thetaAboveCell000032112023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112023 h)

theorem cover_subtree_26949ddfa0ff :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112030
        (by
          have h : ((childLL thetaAboveCell000032112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112030) h)
        (by
          have h : ((childLH thetaAboveCell000032112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112030) h)
        (by
          have h : ((childHL thetaAboveCell000032112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112030) h)
        (by
          have h : ((childHH thetaAboveCell000032112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112031
        (by
          have h : ((childLL thetaAboveCell000032112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112031) h)
        (by
          have h : ((childLH thetaAboveCell000032112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112031) h)
        (by
          have h : ((childHL thetaAboveCell000032112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112031) h)
        (by
          have h : ((childHH thetaAboveCell000032112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112031) h))
    (by
      have h : (thetaAboveCell000032112032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112032 h)
    (by
      have h : (thetaAboveCell000032112033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112033 h)

theorem e24KC2ThetaAboveLeaf0000321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003211))
    cover_subtree_5921e16da435
    cover_subtree_52f1b09bd9bd
    cover_subtree_0a1ef543bda5
    cover_subtree_26949ddfa0ff
theorem cover_subtree_b04014698fa2 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032112100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112100 h)
    (by
      have h : (thetaAboveCell000032112101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112102
        (by
          have h : ((childLL thetaAboveCell000032112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112102) h)
        (by
          have h : ((childLH thetaAboveCell000032112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112102) h)
        (by
          have h : ((childHL thetaAboveCell000032112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112102) h)
        (by
          have h : ((childHH thetaAboveCell000032112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112103
        (by
          have h : ((childLL thetaAboveCell000032112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112103) h)
        (by
          have h : ((childLH thetaAboveCell000032112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112103) h)
        (by
          have h : ((childHL thetaAboveCell000032112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112103) h)
        (by
          have h : ((childHH thetaAboveCell000032112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112103) h))

theorem cover_subtree_49d16aafe784 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032112110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112110 h)
    (by
      have h : (thetaAboveCell000032112111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112112
        (by
          have h : ((childLL thetaAboveCell000032112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112112) h)
        (by
          have h : ((childLH thetaAboveCell000032112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112112) h)
        (by
          have h : ((childHL thetaAboveCell000032112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112112) h)
        (by
          have h : ((childHH thetaAboveCell000032112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112113
        (by
          have h : ((childLL thetaAboveCell000032112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112113) h)
        (by
          have h : ((childLH thetaAboveCell000032112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112113) h)
        (by
          have h : ((childHL thetaAboveCell000032112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112113) h)
        (by
          have h : ((childHH thetaAboveCell000032112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112113) h))

theorem cover_subtree_b7dcbd8da2a4 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112120
        (by
          have h : ((childLL thetaAboveCell000032112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112120) h)
        (by
          have h : ((childLH thetaAboveCell000032112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112120) h)
        (by
          have h : ((childHL thetaAboveCell000032112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112120) h)
        (by
          have h : ((childHH thetaAboveCell000032112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112121
        (by
          have h : ((childLL thetaAboveCell000032112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112121) h)
        (by
          have h : ((childLH thetaAboveCell000032112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112121) h)
        (by
          have h : ((childHL thetaAboveCell000032112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112121) h)
        (by
          have h : ((childHH thetaAboveCell000032112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112121) h))
    (by
      have h : (thetaAboveCell000032112122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112122 h)
    (by
      have h : (thetaAboveCell000032112123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112123 h)

theorem cover_subtree_fb1811cd44df :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112130
        (by
          have h : ((childLL thetaAboveCell000032112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112130) h)
        (by
          have h : ((childLH thetaAboveCell000032112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112130) h)
        (by
          have h : ((childHL thetaAboveCell000032112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112130) h)
        (by
          have h : ((childHH thetaAboveCell000032112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112131
        (by
          have h : ((childLL thetaAboveCell000032112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112131) h)
        (by
          have h : ((childLH thetaAboveCell000032112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112131) h)
        (by
          have h : ((childHL thetaAboveCell000032112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112131) h)
        (by
          have h : ((childHH thetaAboveCell000032112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112131) h))
    (by
      have h : (thetaAboveCell000032112132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112132 h)
    (by
      have h : (thetaAboveCell000032112133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112133 h)

theorem e24KC2ThetaAboveLeaf0000321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003211))
    cover_subtree_b04014698fa2
    cover_subtree_49d16aafe784
    cover_subtree_b7dcbd8da2a4
    cover_subtree_fb1811cd44df
theorem e24KC2ThetaAboveLeaf0000321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003211))) h)
theorem cover_subtree_6f17b9dcfe31 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032113000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113000 h)
    (by
      have h : (thetaAboveCell000032113001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113002
        (by
          have h : ((childLL thetaAboveCell000032113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113002) h)
        (by
          have h : ((childLH thetaAboveCell000032113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113002) h)
        (by
          have h : ((childHL thetaAboveCell000032113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113002) h)
        (by
          have h : ((childHH thetaAboveCell000032113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113003
        (by
          have h : ((childLL thetaAboveCell000032113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113003) h)
        (by
          have h : ((childLH thetaAboveCell000032113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113003) h)
        (by
          have h : ((childHL thetaAboveCell000032113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113003) h)
        (by
          have h : ((childHH thetaAboveCell000032113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113003) h))

theorem cover_subtree_bf78b444527b :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032113010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113010 h)
    (by
      have h : (thetaAboveCell000032113011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113012
        (by
          have h : ((childLL thetaAboveCell000032113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113012) h)
        (by
          have h : ((childLH thetaAboveCell000032113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113012) h)
        (by
          have h : ((childHL thetaAboveCell000032113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113012) h)
        (by
          have h : ((childHH thetaAboveCell000032113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113013
        (by
          have h : ((childLL thetaAboveCell000032113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113013) h)
        (by
          have h : ((childLH thetaAboveCell000032113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113013) h)
        (by
          have h : ((childHL thetaAboveCell000032113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113013) h)
        (by
          have h : ((childHH thetaAboveCell000032113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113013) h))

theorem cover_subtree_68fa0f6b74ff :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113020
        (by
          have h : ((childLL thetaAboveCell000032113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113020) h)
        (by
          have h : ((childLH thetaAboveCell000032113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113020) h)
        (by
          have h : ((childHL thetaAboveCell000032113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113020) h)
        (by
          have h : ((childHH thetaAboveCell000032113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113021
        (by
          have h : ((childLL thetaAboveCell000032113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113021) h)
        (by
          have h : ((childLH thetaAboveCell000032113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113021) h)
        (by
          have h : ((childHL thetaAboveCell000032113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113021) h)
        (by
          have h : ((childHH thetaAboveCell000032113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113021) h))
    (by
      have h : (thetaAboveCell000032113022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113022 h)
    (by
      have h : (thetaAboveCell000032113023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113023 h)

theorem cover_subtree_00b90c74e0b1 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113030
        (by
          have h : ((childLL thetaAboveCell000032113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113030) h)
        (by
          have h : ((childLH thetaAboveCell000032113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113030) h)
        (by
          have h : ((childHL thetaAboveCell000032113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113030) h)
        (by
          have h : ((childHH thetaAboveCell000032113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113031
        (by
          have h : ((childLL thetaAboveCell000032113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113031) h)
        (by
          have h : ((childLH thetaAboveCell000032113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113031) h)
        (by
          have h : ((childHL thetaAboveCell000032113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113031) h)
        (by
          have h : ((childHH thetaAboveCell000032113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113031) h))
    (by
      have h : (thetaAboveCell000032113032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113032 h)
    (by
      have h : (thetaAboveCell000032113033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113033 h)

theorem e24KC2ThetaAboveLeaf0000321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003211))
    cover_subtree_6f17b9dcfe31
    cover_subtree_bf78b444527b
    cover_subtree_68fa0f6b74ff
    cover_subtree_00b90c74e0b1
theorem cover_subtree_bd2e141553af :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032113100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113100 h)
    (by
      have h : (thetaAboveCell000032113101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113102
        (by
          have h : ((childLL thetaAboveCell000032113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113102) h)
        (by
          have h : ((childLH thetaAboveCell000032113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113102) h)
        (by
          have h : ((childHL thetaAboveCell000032113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113102) h)
        (by
          have h : ((childHH thetaAboveCell000032113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113103
        (by
          have h : ((childLL thetaAboveCell000032113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113103) h)
        (by
          have h : ((childLH thetaAboveCell000032113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113103) h)
        (by
          have h : ((childHL thetaAboveCell000032113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113103) h)
        (by
          have h : ((childHH thetaAboveCell000032113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113103) h))

theorem cover_subtree_689bdaf91bf7 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032113110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113110 h)
    (by
      have h : (thetaAboveCell000032113111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113112
        (by
          have h : ((childLL thetaAboveCell000032113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113112) h)
        (by
          have h : ((childLH thetaAboveCell000032113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113112) h)
        (by
          have h : ((childHL thetaAboveCell000032113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113112) h)
        (by
          have h : ((childHH thetaAboveCell000032113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113113
        (by
          have h : ((childLL thetaAboveCell000032113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113113) h)
        (by
          have h : ((childLH thetaAboveCell000032113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113113) h)
        (by
          have h : ((childHL thetaAboveCell000032113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113113) h)
        (by
          have h : ((childHH thetaAboveCell000032113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113113) h))

theorem cover_subtree_0feb1fef76ea :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113120
        (by
          have h : ((childLL thetaAboveCell000032113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113120) h)
        (by
          have h : ((childLH thetaAboveCell000032113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113120) h)
        (by
          have h : ((childHL thetaAboveCell000032113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113120) h)
        (by
          have h : ((childHH thetaAboveCell000032113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113121
        (by
          have h : ((childLL thetaAboveCell000032113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113121) h)
        (by
          have h : ((childLH thetaAboveCell000032113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113121) h)
        (by
          have h : ((childHL thetaAboveCell000032113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113121) h)
        (by
          have h : ((childHH thetaAboveCell000032113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113121) h))
    (by
      have h : (thetaAboveCell000032113122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113122 h)
    (by
      have h : (thetaAboveCell000032113123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113123 h)

theorem cover_subtree_5f404684ac08 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113130
        (by
          have h : ((childLL thetaAboveCell000032113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113130) h)
        (by
          have h : ((childLH thetaAboveCell000032113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113130) h)
        (by
          have h : ((childHL thetaAboveCell000032113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113130) h)
        (by
          have h : ((childHH thetaAboveCell000032113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113131
        (by
          have h : ((childLL thetaAboveCell000032113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113131) h)
        (by
          have h : ((childLH thetaAboveCell000032113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113131) h)
        (by
          have h : ((childHL thetaAboveCell000032113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113131) h)
        (by
          have h : ((childHH thetaAboveCell000032113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113131) h))
    (by
      have h : (thetaAboveCell000032113132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113132 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113133
        (by
          have h : ((childLL thetaAboveCell000032113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113133) h)
        (by
          have h : ((childLH thetaAboveCell000032113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113133) h)
        (by
          have h : ((childHL thetaAboveCell000032113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113133) h)
        (by
          have h : ((childHH thetaAboveCell000032113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113133) h))

theorem e24KC2ThetaAboveLeaf0000321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003211))
    cover_subtree_bd2e141553af
    cover_subtree_689bdaf91bf7
    cover_subtree_0feb1fef76ea
    cover_subtree_5f404684ac08
theorem e24KC2ThetaAboveLeaf0000321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000330002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003300))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003300))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003300))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003300))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003300))) h)
theorem cover_subtree_307fcc32307f :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033002000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002000 h)
    (by
      have h : (thetaAboveCell000033002001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002002
        (by
          have h : ((childLL thetaAboveCell000033002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002002) h)
        (by
          have h : ((childLH thetaAboveCell000033002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002002) h)
        (by
          have h : ((childHL thetaAboveCell000033002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002002) h)
        (by
          have h : ((childHH thetaAboveCell000033002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002003
        (by
          have h : ((childLL thetaAboveCell000033002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002003) h)
        (by
          have h : ((childLH thetaAboveCell000033002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002003) h)
        (by
          have h : ((childHL thetaAboveCell000033002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002003) h)
        (by
          have h : ((childHH thetaAboveCell000033002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002003) h))

theorem cover_subtree_d72d916d3b48 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033002010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002010 h)
    (by
      have h : (thetaAboveCell000033002011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002012
        (by
          have h : ((childLL thetaAboveCell000033002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002012) h)
        (by
          have h : ((childLH thetaAboveCell000033002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002012) h)
        (by
          have h : ((childHL thetaAboveCell000033002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002012) h)
        (by
          have h : ((childHH thetaAboveCell000033002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002013
        (by
          have h : ((childLL thetaAboveCell000033002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002013) h)
        (by
          have h : ((childLH thetaAboveCell000033002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002013) h)
        (by
          have h : ((childHL thetaAboveCell000033002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002013) h)
        (by
          have h : ((childHH thetaAboveCell000033002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002013) h))

theorem cover_subtree_68d4094c9ee3 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002020
        (by
          have h : ((childLL thetaAboveCell000033002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002020) h)
        (by
          have h : ((childLH thetaAboveCell000033002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002020) h)
        (by
          have h : ((childHL thetaAboveCell000033002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002020) h)
        (by
          have h : ((childHH thetaAboveCell000033002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002021
        (by
          have h : ((childLL thetaAboveCell000033002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002021) h)
        (by
          have h : ((childLH thetaAboveCell000033002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002021) h)
        (by
          have h : ((childHL thetaAboveCell000033002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002021) h)
        (by
          have h : ((childHH thetaAboveCell000033002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002022
        (by
          have h : ((childLL thetaAboveCell000033002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002022) h)
        (by
          have h : ((childLH thetaAboveCell000033002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002022) h)
        (by
          have h : ((childHL thetaAboveCell000033002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002022) h)
        (by
          have h : ((childHH thetaAboveCell000033002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002023
        (by
          have h : ((childLL thetaAboveCell000033002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002023) h)
        (by
          have h : ((childLH thetaAboveCell000033002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002023) h)
        (by
          have h : ((childHL thetaAboveCell000033002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002023) h)
        (by
          have h : ((childHH thetaAboveCell000033002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002023) h))

theorem cover_subtree_133a2eba8f2a :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002030
        (by
          have h : ((childLL thetaAboveCell000033002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002030) h)
        (by
          have h : ((childLH thetaAboveCell000033002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002030) h)
        (by
          have h : ((childHL thetaAboveCell000033002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002030) h)
        (by
          have h : ((childHH thetaAboveCell000033002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002031
        (by
          have h : ((childLL thetaAboveCell000033002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002031) h)
        (by
          have h : ((childLH thetaAboveCell000033002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002031) h)
        (by
          have h : ((childHL thetaAboveCell000033002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002031) h)
        (by
          have h : ((childHH thetaAboveCell000033002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002032
        (by
          have h : ((childLL thetaAboveCell000033002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002032) h)
        (by
          have h : ((childLH thetaAboveCell000033002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002032) h)
        (by
          have h : ((childHL thetaAboveCell000033002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002032) h)
        (by
          have h : ((childHH thetaAboveCell000033002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002033
        (by
          have h : ((childLL thetaAboveCell000033002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002033) h)
        (by
          have h : ((childLH thetaAboveCell000033002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002033) h)
        (by
          have h : ((childHL thetaAboveCell000033002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002033) h)
        (by
          have h : ((childHH thetaAboveCell000033002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002033) h))

theorem e24KC2ThetaAboveLeaf0000330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003300))
    cover_subtree_307fcc32307f
    cover_subtree_d72d916d3b48
    cover_subtree_68d4094c9ee3
    cover_subtree_133a2eba8f2a
theorem cover_subtree_81e0e7f5c28b :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033002100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002100 h)
    (by
      have h : (thetaAboveCell000033002101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002102
        (by
          have h : ((childLL thetaAboveCell000033002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002102) h)
        (by
          have h : ((childLH thetaAboveCell000033002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002102) h)
        (by
          have h : ((childHL thetaAboveCell000033002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002102) h)
        (by
          have h : ((childHH thetaAboveCell000033002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002103
        (by
          have h : ((childLL thetaAboveCell000033002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002103) h)
        (by
          have h : ((childLH thetaAboveCell000033002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002103) h)
        (by
          have h : ((childHL thetaAboveCell000033002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002103) h)
        (by
          have h : ((childHH thetaAboveCell000033002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002103) h))

theorem cover_subtree_db4d96344863 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033002110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002110 h)
    (by
      have h : (thetaAboveCell000033002111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002112
        (by
          have h : ((childLL thetaAboveCell000033002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002112) h)
        (by
          have h : ((childLH thetaAboveCell000033002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002112) h)
        (by
          have h : ((childHL thetaAboveCell000033002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002112) h)
        (by
          have h : ((childHH thetaAboveCell000033002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002113
        (by
          have h : ((childLL thetaAboveCell000033002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002113) h)
        (by
          have h : ((childLH thetaAboveCell000033002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002113) h)
        (by
          have h : ((childHL thetaAboveCell000033002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002113) h)
        (by
          have h : ((childHH thetaAboveCell000033002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002113) h))

theorem cover_subtree_f83decf107d3 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002120
        (by
          have h : ((childLL thetaAboveCell000033002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002120) h)
        (by
          have h : ((childLH thetaAboveCell000033002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002120) h)
        (by
          have h : ((childHL thetaAboveCell000033002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002120) h)
        (by
          have h : ((childHH thetaAboveCell000033002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002121
        (by
          have h : ((childLL thetaAboveCell000033002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002121) h)
        (by
          have h : ((childLH thetaAboveCell000033002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002121) h)
        (by
          have h : ((childHL thetaAboveCell000033002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002121) h)
        (by
          have h : ((childHH thetaAboveCell000033002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002122
        (by
          have h : ((childLL thetaAboveCell000033002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002122) h)
        (by
          have h : ((childLH thetaAboveCell000033002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002122) h)
        (by
          have h : ((childHL thetaAboveCell000033002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002122) h)
        (by
          have h : ((childHH thetaAboveCell000033002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002123
        (by
          have h : ((childLL thetaAboveCell000033002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002123) h)
        (by
          have h : ((childLH thetaAboveCell000033002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002123) h)
        (by
          have h : ((childHL thetaAboveCell000033002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002123) h)
        (by
          have h : ((childHH thetaAboveCell000033002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002123) h))

theorem cover_subtree_aa2cd6339b25 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002130
        (by
          have h : ((childLL thetaAboveCell000033002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002130) h)
        (by
          have h : ((childLH thetaAboveCell000033002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002130) h)
        (by
          have h : ((childHL thetaAboveCell000033002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002130) h)
        (by
          have h : ((childHH thetaAboveCell000033002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002131
        (by
          have h : ((childLL thetaAboveCell000033002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002131) h)
        (by
          have h : ((childLH thetaAboveCell000033002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002131) h)
        (by
          have h : ((childHL thetaAboveCell000033002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002131) h)
        (by
          have h : ((childHH thetaAboveCell000033002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002132
        (by
          have h : ((childLL thetaAboveCell000033002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002132) h)
        (by
          have h : ((childLH thetaAboveCell000033002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002132) h)
        (by
          have h : ((childHL thetaAboveCell000033002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002132) h)
        (by
          have h : ((childHH thetaAboveCell000033002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002133
        (by
          have h : ((childLL thetaAboveCell000033002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002133) h)
        (by
          have h : ((childLH thetaAboveCell000033002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002133) h)
        (by
          have h : ((childHL thetaAboveCell000033002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002133) h)
        (by
          have h : ((childHH thetaAboveCell000033002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002133) h))

theorem e24KC2ThetaAboveLeaf0000330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003300))
    cover_subtree_81e0e7f5c28b
    cover_subtree_db4d96344863
    cover_subtree_f83decf107d3
    cover_subtree_aa2cd6339b25
theorem e24KC2ThetaAboveLeaf0000330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003300))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003300))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003300))) h)
theorem cover_subtree_9d0a80f57bd8 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033003000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003000 h)
    (by
      have h : (thetaAboveCell000033003001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003002
        (by
          have h : ((childLL thetaAboveCell000033003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003002) h)
        (by
          have h : ((childLH thetaAboveCell000033003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003002) h)
        (by
          have h : ((childHL thetaAboveCell000033003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003002) h)
        (by
          have h : ((childHH thetaAboveCell000033003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003003
        (by
          have h : ((childLL thetaAboveCell000033003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003003) h)
        (by
          have h : ((childLH thetaAboveCell000033003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003003) h)
        (by
          have h : ((childHL thetaAboveCell000033003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003003) h)
        (by
          have h : ((childHH thetaAboveCell000033003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003003) h))

theorem cover_subtree_dc4f306f6518 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033003010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003010 h)
    (by
      have h : (thetaAboveCell000033003011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003012
        (by
          have h : ((childLL thetaAboveCell000033003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003012) h)
        (by
          have h : ((childLH thetaAboveCell000033003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003012) h)
        (by
          have h : ((childHL thetaAboveCell000033003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003012) h)
        (by
          have h : ((childHH thetaAboveCell000033003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003013
        (by
          have h : ((childLL thetaAboveCell000033003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003013) h)
        (by
          have h : ((childLH thetaAboveCell000033003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003013) h)
        (by
          have h : ((childHL thetaAboveCell000033003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003013) h)
        (by
          have h : ((childHH thetaAboveCell000033003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003013) h))

theorem cover_subtree_f02da567f8d1 :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003020
        (by
          have h : ((childLL thetaAboveCell000033003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003020) h)
        (by
          have h : ((childLH thetaAboveCell000033003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003020) h)
        (by
          have h : ((childHL thetaAboveCell000033003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003020) h)
        (by
          have h : ((childHH thetaAboveCell000033003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003021
        (by
          have h : ((childLL thetaAboveCell000033003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003021) h)
        (by
          have h : ((childLH thetaAboveCell000033003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003021) h)
        (by
          have h : ((childHL thetaAboveCell000033003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003021) h)
        (by
          have h : ((childHH thetaAboveCell000033003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003022
        (by
          have h : ((childLL thetaAboveCell000033003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003022) h)
        (by
          have h : ((childLH thetaAboveCell000033003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003022) h)
        (by
          have h : ((childHL thetaAboveCell000033003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003022) h)
        (by
          have h : ((childHH thetaAboveCell000033003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003023
        (by
          have h : ((childLL thetaAboveCell000033003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003023) h)
        (by
          have h : ((childLH thetaAboveCell000033003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003023) h)
        (by
          have h : ((childHL thetaAboveCell000033003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003023) h)
        (by
          have h : ((childHH thetaAboveCell000033003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003023) h))

theorem cover_subtree_5b244ca5864c :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003030
        (by
          have h : ((childLL thetaAboveCell000033003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003030) h)
        (by
          have h : ((childLH thetaAboveCell000033003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003030) h)
        (by
          have h : ((childHL thetaAboveCell000033003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003030) h)
        (by
          have h : ((childHH thetaAboveCell000033003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003031
        (by
          have h : ((childLL thetaAboveCell000033003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003031) h)
        (by
          have h : ((childLH thetaAboveCell000033003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003031) h)
        (by
          have h : ((childHL thetaAboveCell000033003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003031) h)
        (by
          have h : ((childHH thetaAboveCell000033003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003032
        (by
          have h : ((childLL thetaAboveCell000033003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003032) h)
        (by
          have h : ((childLH thetaAboveCell000033003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003032) h)
        (by
          have h : ((childHL thetaAboveCell000033003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003032) h)
        (by
          have h : ((childHH thetaAboveCell000033003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003033
        (by
          have h : ((childLL thetaAboveCell000033003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003033) h)
        (by
          have h : ((childLH thetaAboveCell000033003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003033) h)
        (by
          have h : ((childHL thetaAboveCell000033003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003033) h)
        (by
          have h : ((childHH thetaAboveCell000033003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003033) h))

theorem e24KC2ThetaAboveLeaf0000330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003300))
    cover_subtree_9d0a80f57bd8
    cover_subtree_dc4f306f6518
    cover_subtree_f02da567f8d1
    cover_subtree_5b244ca5864c
theorem cover_subtree_834d2353fe6e :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033003100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003100 h)
    (by
      have h : (thetaAboveCell000033003101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003102
        (by
          have h : ((childLL thetaAboveCell000033003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003102) h)
        (by
          have h : ((childLH thetaAboveCell000033003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003102) h)
        (by
          have h : ((childHL thetaAboveCell000033003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003102) h)
        (by
          have h : ((childHH thetaAboveCell000033003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003103
        (by
          have h : ((childLL thetaAboveCell000033003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003103) h)
        (by
          have h : ((childLH thetaAboveCell000033003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003103) h)
        (by
          have h : ((childHL thetaAboveCell000033003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003103) h)
        (by
          have h : ((childHH thetaAboveCell000033003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003103) h))

theorem cover_subtree_d145e983fe8d :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033003110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003110 h)
    (by
      have h : (thetaAboveCell000033003111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003112
        (by
          have h : ((childLL thetaAboveCell000033003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003112) h)
        (by
          have h : ((childLH thetaAboveCell000033003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003112) h)
        (by
          have h : ((childHL thetaAboveCell000033003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003112) h)
        (by
          have h : ((childHH thetaAboveCell000033003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003113
        (by
          have h : ((childLL thetaAboveCell000033003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003113) h)
        (by
          have h : ((childLH thetaAboveCell000033003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003113) h)
        (by
          have h : ((childHL thetaAboveCell000033003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003113) h)
        (by
          have h : ((childHH thetaAboveCell000033003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003113) h))

theorem cover_subtree_d12e61a2b3bb :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003120
        (by
          have h : ((childLL thetaAboveCell000033003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003120) h)
        (by
          have h : ((childLH thetaAboveCell000033003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003120) h)
        (by
          have h : ((childHL thetaAboveCell000033003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003120) h)
        (by
          have h : ((childHH thetaAboveCell000033003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003121
        (by
          have h : ((childLL thetaAboveCell000033003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003121) h)
        (by
          have h : ((childLH thetaAboveCell000033003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003121) h)
        (by
          have h : ((childHL thetaAboveCell000033003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003121) h)
        (by
          have h : ((childHH thetaAboveCell000033003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003122
        (by
          have h : ((childLL thetaAboveCell000033003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003122) h)
        (by
          have h : ((childLH thetaAboveCell000033003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003122) h)
        (by
          have h : ((childHL thetaAboveCell000033003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003122) h)
        (by
          have h : ((childHH thetaAboveCell000033003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003123
        (by
          have h : ((childLL thetaAboveCell000033003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003123) h)
        (by
          have h : ((childLH thetaAboveCell000033003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003123) h)
        (by
          have h : ((childHL thetaAboveCell000033003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003123) h)
        (by
          have h : ((childHH thetaAboveCell000033003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003123) h))

theorem cover_subtree_19725b594124 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003130
        (by
          have h : ((childLL thetaAboveCell000033003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003130) h)
        (by
          have h : ((childLH thetaAboveCell000033003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003130) h)
        (by
          have h : ((childHL thetaAboveCell000033003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003130) h)
        (by
          have h : ((childHH thetaAboveCell000033003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003131
        (by
          have h : ((childLL thetaAboveCell000033003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003131) h)
        (by
          have h : ((childLH thetaAboveCell000033003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003131) h)
        (by
          have h : ((childHL thetaAboveCell000033003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003131) h)
        (by
          have h : ((childHH thetaAboveCell000033003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003132
        (by
          have h : ((childLL thetaAboveCell000033003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003132) h)
        (by
          have h : ((childLH thetaAboveCell000033003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003132) h)
        (by
          have h : ((childHL thetaAboveCell000033003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003132) h)
        (by
          have h : ((childHH thetaAboveCell000033003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003133
        (by
          have h : ((childLL thetaAboveCell000033003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003133) h)
        (by
          have h : ((childLH thetaAboveCell000033003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003133) h)
        (by
          have h : ((childHL thetaAboveCell000033003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003133) h)
        (by
          have h : ((childHH thetaAboveCell000033003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003133) h))

theorem e24KC2ThetaAboveLeaf0000330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003300))
    cover_subtree_834d2353fe6e
    cover_subtree_d145e983fe8d
    cover_subtree_d12e61a2b3bb
    cover_subtree_19725b594124
theorem e24KC2ThetaAboveLeaf0000330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003300))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003300))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003301))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003301))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003301))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003301))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003301))) h)
theorem cover_subtree_8335c3bf0b1b :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033012000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012000 h)
    (by
      have h : (thetaAboveCell000033012001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012002
        (by
          have h : ((childLL thetaAboveCell000033012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012002) h)
        (by
          have h : ((childLH thetaAboveCell000033012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012002) h)
        (by
          have h : ((childHL thetaAboveCell000033012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012002) h)
        (by
          have h : ((childHH thetaAboveCell000033012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012003
        (by
          have h : ((childLL thetaAboveCell000033012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012003) h)
        (by
          have h : ((childLH thetaAboveCell000033012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012003) h)
        (by
          have h : ((childHL thetaAboveCell000033012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012003) h)
        (by
          have h : ((childHH thetaAboveCell000033012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012003) h))

theorem cover_subtree_020729332332 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033012010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012010 h)
    (by
      have h : (thetaAboveCell000033012011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012012
        (by
          have h : ((childLL thetaAboveCell000033012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012012) h)
        (by
          have h : ((childLH thetaAboveCell000033012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012012) h)
        (by
          have h : ((childHL thetaAboveCell000033012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012012) h)
        (by
          have h : ((childHH thetaAboveCell000033012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012013
        (by
          have h : ((childLL thetaAboveCell000033012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012013) h)
        (by
          have h : ((childLH thetaAboveCell000033012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012013) h)
        (by
          have h : ((childHL thetaAboveCell000033012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012013) h)
        (by
          have h : ((childHH thetaAboveCell000033012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012013) h))

theorem cover_subtree_f21e4f8d9787 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012020
        (by
          have h : ((childLL thetaAboveCell000033012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012020) h)
        (by
          have h : ((childLH thetaAboveCell000033012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012020) h)
        (by
          have h : ((childHL thetaAboveCell000033012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012020) h)
        (by
          have h : ((childHH thetaAboveCell000033012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012021
        (by
          have h : ((childLL thetaAboveCell000033012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012021) h)
        (by
          have h : ((childLH thetaAboveCell000033012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012021) h)
        (by
          have h : ((childHL thetaAboveCell000033012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012021) h)
        (by
          have h : ((childHH thetaAboveCell000033012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012022
        (by
          have h : ((childLL thetaAboveCell000033012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012022) h)
        (by
          have h : ((childLH thetaAboveCell000033012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012022) h)
        (by
          have h : ((childHL thetaAboveCell000033012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012022) h)
        (by
          have h : ((childHH thetaAboveCell000033012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012023
        (by
          have h : ((childLL thetaAboveCell000033012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012023) h)
        (by
          have h : ((childLH thetaAboveCell000033012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012023) h)
        (by
          have h : ((childHL thetaAboveCell000033012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012023) h)
        (by
          have h : ((childHH thetaAboveCell000033012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012023) h))

theorem cover_subtree_bb534365ac4e :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012030
        (by
          have h : ((childLL thetaAboveCell000033012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012030) h)
        (by
          have h : ((childLH thetaAboveCell000033012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012030) h)
        (by
          have h : ((childHL thetaAboveCell000033012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012030) h)
        (by
          have h : ((childHH thetaAboveCell000033012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012031
        (by
          have h : ((childLL thetaAboveCell000033012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012031) h)
        (by
          have h : ((childLH thetaAboveCell000033012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012031) h)
        (by
          have h : ((childHL thetaAboveCell000033012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012031) h)
        (by
          have h : ((childHH thetaAboveCell000033012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012032
        (by
          have h : ((childLL thetaAboveCell000033012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012032) h)
        (by
          have h : ((childLH thetaAboveCell000033012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012032) h)
        (by
          have h : ((childHL thetaAboveCell000033012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012032) h)
        (by
          have h : ((childHH thetaAboveCell000033012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012033
        (by
          have h : ((childLL thetaAboveCell000033012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012033) h)
        (by
          have h : ((childLH thetaAboveCell000033012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012033) h)
        (by
          have h : ((childHL thetaAboveCell000033012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012033) h)
        (by
          have h : ((childHH thetaAboveCell000033012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012033) h))

theorem e24KC2ThetaAboveLeaf0000330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003301))
    cover_subtree_8335c3bf0b1b
    cover_subtree_020729332332
    cover_subtree_f21e4f8d9787
    cover_subtree_bb534365ac4e
theorem cover_subtree_2bf93d8ac027 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033012100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012100 h)
    (by
      have h : (thetaAboveCell000033012101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012102
        (by
          have h : ((childLL thetaAboveCell000033012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012102) h)
        (by
          have h : ((childLH thetaAboveCell000033012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012102) h)
        (by
          have h : ((childHL thetaAboveCell000033012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012102) h)
        (by
          have h : ((childHH thetaAboveCell000033012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012103
        (by
          have h : ((childLL thetaAboveCell000033012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012103) h)
        (by
          have h : ((childLH thetaAboveCell000033012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012103) h)
        (by
          have h : ((childHL thetaAboveCell000033012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012103) h)
        (by
          have h : ((childHH thetaAboveCell000033012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012103) h))

theorem cover_subtree_1f4c8299dae5 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033012110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012110 h)
    (by
      have h : (thetaAboveCell000033012111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012112
        (by
          have h : ((childLL thetaAboveCell000033012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012112) h)
        (by
          have h : ((childLH thetaAboveCell000033012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012112) h)
        (by
          have h : ((childHL thetaAboveCell000033012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012112) h)
        (by
          have h : ((childHH thetaAboveCell000033012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012113
        (by
          have h : ((childLL thetaAboveCell000033012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012113) h)
        (by
          have h : ((childLH thetaAboveCell000033012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012113) h)
        (by
          have h : ((childHL thetaAboveCell000033012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012113) h)
        (by
          have h : ((childHH thetaAboveCell000033012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012113) h))

theorem cover_subtree_6e263eab4641 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012120
        (by
          have h : ((childLL thetaAboveCell000033012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012120) h)
        (by
          have h : ((childLH thetaAboveCell000033012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012120) h)
        (by
          have h : ((childHL thetaAboveCell000033012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012120) h)
        (by
          have h : ((childHH thetaAboveCell000033012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012121
        (by
          have h : ((childLL thetaAboveCell000033012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012121) h)
        (by
          have h : ((childLH thetaAboveCell000033012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012121) h)
        (by
          have h : ((childHL thetaAboveCell000033012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012121) h)
        (by
          have h : ((childHH thetaAboveCell000033012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012122
        (by
          have h : ((childLL thetaAboveCell000033012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012122) h)
        (by
          have h : ((childLH thetaAboveCell000033012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012122) h)
        (by
          have h : ((childHL thetaAboveCell000033012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012122) h)
        (by
          have h : ((childHH thetaAboveCell000033012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012123
        (by
          have h : ((childLL thetaAboveCell000033012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012123) h)
        (by
          have h : ((childLH thetaAboveCell000033012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012123) h)
        (by
          have h : ((childHL thetaAboveCell000033012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012123) h)
        (by
          have h : ((childHH thetaAboveCell000033012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012123) h))

theorem cover_subtree_d9fe12f58957 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012130
        (by
          have h : ((childLL thetaAboveCell000033012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012130) h)
        (by
          have h : ((childLH thetaAboveCell000033012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012130) h)
        (by
          have h : ((childHL thetaAboveCell000033012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012130) h)
        (by
          have h : ((childHH thetaAboveCell000033012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012131
        (by
          have h : ((childLL thetaAboveCell000033012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012131) h)
        (by
          have h : ((childLH thetaAboveCell000033012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012131) h)
        (by
          have h : ((childHL thetaAboveCell000033012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012131) h)
        (by
          have h : ((childHH thetaAboveCell000033012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012132
        (by
          have h : ((childLL thetaAboveCell000033012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012132) h)
        (by
          have h : ((childLH thetaAboveCell000033012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012132) h)
        (by
          have h : ((childHL thetaAboveCell000033012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012132) h)
        (by
          have h : ((childHH thetaAboveCell000033012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012133
        (by
          have h : ((childLL thetaAboveCell000033012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012133) h)
        (by
          have h : ((childLH thetaAboveCell000033012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012133) h)
        (by
          have h : ((childHL thetaAboveCell000033012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012133) h)
        (by
          have h : ((childHH thetaAboveCell000033012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012133) h))

theorem e24KC2ThetaAboveLeaf0000330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003301))
    cover_subtree_2bf93d8ac027
    cover_subtree_1f4c8299dae5
    cover_subtree_6e263eab4641
    cover_subtree_d9fe12f58957
theorem e24KC2ThetaAboveLeaf0000330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012200 h)
        (by
          have h : (thetaAboveCell000033012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012201 h)
        (by
          have h : (thetaAboveCell000033012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012202 h)
        (by
          have h : (thetaAboveCell000033012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012210 h)
        (by
          have h : (thetaAboveCell000033012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012211 h)
        (by
          have h : (thetaAboveCell000033012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012212 h)
        (by
          have h : (thetaAboveCell000033012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012300 h)
        (by
          have h : (thetaAboveCell000033012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012301 h)
        (by
          have h : (thetaAboveCell000033012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012302 h)
        (by
          have h : (thetaAboveCell000033012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012310 h)
        (by
          have h : (thetaAboveCell000033012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012311 h)
        (by
          have h : (thetaAboveCell000033012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012312 h)
        (by
          have h : (thetaAboveCell000033012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003301))) h)
theorem cover_subtree_3ee7d70a5db3 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033013000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013000 h)
    (by
      have h : (thetaAboveCell000033013001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013002
        (by
          have h : ((childLL thetaAboveCell000033013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013002) h)
        (by
          have h : ((childLH thetaAboveCell000033013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013002) h)
        (by
          have h : ((childHL thetaAboveCell000033013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013002) h)
        (by
          have h : ((childHH thetaAboveCell000033013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013003
        (by
          have h : ((childLL thetaAboveCell000033013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013003) h)
        (by
          have h : ((childLH thetaAboveCell000033013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013003) h)
        (by
          have h : ((childHL thetaAboveCell000033013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013003) h)
        (by
          have h : ((childHH thetaAboveCell000033013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013003) h))

theorem cover_subtree_f6080530d2a9 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033013010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013010 h)
    (by
      have h : (thetaAboveCell000033013011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013012
        (by
          have h : ((childLL thetaAboveCell000033013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013012) h)
        (by
          have h : ((childLH thetaAboveCell000033013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013012) h)
        (by
          have h : ((childHL thetaAboveCell000033013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013012) h)
        (by
          have h : ((childHH thetaAboveCell000033013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013013
        (by
          have h : ((childLL thetaAboveCell000033013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013013) h)
        (by
          have h : ((childLH thetaAboveCell000033013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013013) h)
        (by
          have h : ((childHL thetaAboveCell000033013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013013) h)
        (by
          have h : ((childHH thetaAboveCell000033013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013013) h))

theorem cover_subtree_2e5606e732f5 :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013020
        (by
          have h : ((childLL thetaAboveCell000033013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013020) h)
        (by
          have h : ((childLH thetaAboveCell000033013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013020) h)
        (by
          have h : ((childHL thetaAboveCell000033013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013020) h)
        (by
          have h : ((childHH thetaAboveCell000033013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013021
        (by
          have h : ((childLL thetaAboveCell000033013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013021) h)
        (by
          have h : ((childLH thetaAboveCell000033013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013021) h)
        (by
          have h : ((childHL thetaAboveCell000033013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013021) h)
        (by
          have h : ((childHH thetaAboveCell000033013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013022
        (by
          have h : ((childLL thetaAboveCell000033013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013022) h)
        (by
          have h : ((childLH thetaAboveCell000033013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013022) h)
        (by
          have h : ((childHL thetaAboveCell000033013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013022) h)
        (by
          have h : ((childHH thetaAboveCell000033013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013023
        (by
          have h : ((childLL thetaAboveCell000033013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013023) h)
        (by
          have h : ((childLH thetaAboveCell000033013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013023) h)
        (by
          have h : ((childHL thetaAboveCell000033013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013023) h)
        (by
          have h : ((childHH thetaAboveCell000033013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013023) h))

theorem cover_subtree_6143158a1495 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013030
        (by
          have h : ((childLL thetaAboveCell000033013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013030) h)
        (by
          have h : ((childLH thetaAboveCell000033013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013030) h)
        (by
          have h : ((childHL thetaAboveCell000033013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013030) h)
        (by
          have h : ((childHH thetaAboveCell000033013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013031
        (by
          have h : ((childLL thetaAboveCell000033013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013031) h)
        (by
          have h : ((childLH thetaAboveCell000033013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013031) h)
        (by
          have h : ((childHL thetaAboveCell000033013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013031) h)
        (by
          have h : ((childHH thetaAboveCell000033013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013032
        (by
          have h : ((childLL thetaAboveCell000033013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013032) h)
        (by
          have h : ((childLH thetaAboveCell000033013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013032) h)
        (by
          have h : ((childHL thetaAboveCell000033013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013032) h)
        (by
          have h : ((childHH thetaAboveCell000033013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013033
        (by
          have h : ((childLL thetaAboveCell000033013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013033) h)
        (by
          have h : ((childLH thetaAboveCell000033013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013033) h)
        (by
          have h : ((childHL thetaAboveCell000033013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013033) h)
        (by
          have h : ((childHH thetaAboveCell000033013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013033) h))

theorem e24KC2ThetaAboveLeaf0000330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003301))
    cover_subtree_3ee7d70a5db3
    cover_subtree_f6080530d2a9
    cover_subtree_2e5606e732f5
    cover_subtree_6143158a1495
theorem cover_subtree_fd7379f50292 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033013100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013100 h)
    (by
      have h : (thetaAboveCell000033013101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013102
        (by
          have h : ((childLL thetaAboveCell000033013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013102) h)
        (by
          have h : ((childLH thetaAboveCell000033013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013102) h)
        (by
          have h : ((childHL thetaAboveCell000033013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013102) h)
        (by
          have h : ((childHH thetaAboveCell000033013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013103
        (by
          have h : ((childLL thetaAboveCell000033013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013103) h)
        (by
          have h : ((childLH thetaAboveCell000033013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013103) h)
        (by
          have h : ((childHL thetaAboveCell000033013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013103) h)
        (by
          have h : ((childHH thetaAboveCell000033013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013103) h))

theorem cover_subtree_f974def6b3e0 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033013110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013110 h)
    (by
      have h : (thetaAboveCell000033013111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013112
        (by
          have h : ((childLL thetaAboveCell000033013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013112) h)
        (by
          have h : ((childLH thetaAboveCell000033013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013112) h)
        (by
          have h : ((childHL thetaAboveCell000033013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013112) h)
        (by
          have h : ((childHH thetaAboveCell000033013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013113
        (by
          have h : ((childLL thetaAboveCell000033013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013113) h)
        (by
          have h : ((childLH thetaAboveCell000033013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013113) h)
        (by
          have h : ((childHL thetaAboveCell000033013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013113) h)
        (by
          have h : ((childHH thetaAboveCell000033013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013113) h))

theorem cover_subtree_d879dc743b47 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013120
        (by
          have h : ((childLL thetaAboveCell000033013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013120) h)
        (by
          have h : ((childLH thetaAboveCell000033013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013120) h)
        (by
          have h : ((childHL thetaAboveCell000033013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013120) h)
        (by
          have h : ((childHH thetaAboveCell000033013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013121
        (by
          have h : ((childLL thetaAboveCell000033013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013121) h)
        (by
          have h : ((childLH thetaAboveCell000033013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013121) h)
        (by
          have h : ((childHL thetaAboveCell000033013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013121) h)
        (by
          have h : ((childHH thetaAboveCell000033013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013122
        (by
          have h : ((childLL thetaAboveCell000033013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013122) h)
        (by
          have h : ((childLH thetaAboveCell000033013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013122) h)
        (by
          have h : ((childHL thetaAboveCell000033013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013122) h)
        (by
          have h : ((childHH thetaAboveCell000033013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013123
        (by
          have h : ((childLL thetaAboveCell000033013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013123) h)
        (by
          have h : ((childLH thetaAboveCell000033013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013123) h)
        (by
          have h : ((childHL thetaAboveCell000033013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013123) h)
        (by
          have h : ((childHH thetaAboveCell000033013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013123) h))

theorem cover_subtree_ebda71a3a487 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013130
        (by
          have h : ((childLL thetaAboveCell000033013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013130) h)
        (by
          have h : ((childLH thetaAboveCell000033013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013130) h)
        (by
          have h : ((childHL thetaAboveCell000033013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013130) h)
        (by
          have h : ((childHH thetaAboveCell000033013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013131
        (by
          have h : ((childLL thetaAboveCell000033013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013131) h)
        (by
          have h : ((childLH thetaAboveCell000033013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013131) h)
        (by
          have h : ((childHL thetaAboveCell000033013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013131) h)
        (by
          have h : ((childHH thetaAboveCell000033013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013132
        (by
          have h : ((childLL thetaAboveCell000033013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013132) h)
        (by
          have h : ((childLH thetaAboveCell000033013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013132) h)
        (by
          have h : ((childHL thetaAboveCell000033013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013132) h)
        (by
          have h : ((childHH thetaAboveCell000033013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013133
        (by
          have h : ((childLL thetaAboveCell000033013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013133) h)
        (by
          have h : ((childLH thetaAboveCell000033013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013133) h)
        (by
          have h : ((childHL thetaAboveCell000033013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013133) h)
        (by
          have h : ((childHH thetaAboveCell000033013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013133) h))

theorem e24KC2ThetaAboveLeaf0000330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003301))
    cover_subtree_fd7379f50292
    cover_subtree_f974def6b3e0
    cover_subtree_d879dc743b47
    cover_subtree_ebda71a3a487
theorem e24KC2ThetaAboveLeaf0000330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013200 h)
        (by
          have h : (thetaAboveCell000033013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013201 h)
        (by
          have h : (thetaAboveCell000033013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013202 h)
        (by
          have h : (thetaAboveCell000033013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013210 h)
        (by
          have h : (thetaAboveCell000033013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013211 h)
        (by
          have h : (thetaAboveCell000033013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013212 h)
        (by
          have h : (thetaAboveCell000033013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013300 h)
        (by
          have h : (thetaAboveCell000033013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013301 h)
        (by
          have h : (thetaAboveCell000033013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013302 h)
        (by
          have h : (thetaAboveCell000033013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013310 h)
        (by
          have h : (thetaAboveCell000033013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013311 h)
        (by
          have h : (thetaAboveCell000033013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013312 h)
        (by
          have h : (thetaAboveCell000033013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000331002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003310))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003310))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003310))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003310))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003310))) h)
theorem cover_subtree_01b17a5cfced :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033102000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102000 h)
    (by
      have h : (thetaAboveCell000033102001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102002
        (by
          have h : ((childLL thetaAboveCell000033102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102002) h)
        (by
          have h : ((childLH thetaAboveCell000033102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102002) h)
        (by
          have h : ((childHL thetaAboveCell000033102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102002) h)
        (by
          have h : ((childHH thetaAboveCell000033102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102003
        (by
          have h : ((childLL thetaAboveCell000033102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102003) h)
        (by
          have h : ((childLH thetaAboveCell000033102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102003) h)
        (by
          have h : ((childHL thetaAboveCell000033102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102003) h)
        (by
          have h : ((childHH thetaAboveCell000033102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102003) h))

theorem cover_subtree_26a3db88cf1e :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033102010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102010 h)
    (by
      have h : (thetaAboveCell000033102011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102012
        (by
          have h : ((childLL thetaAboveCell000033102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102012) h)
        (by
          have h : ((childLH thetaAboveCell000033102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102012) h)
        (by
          have h : ((childHL thetaAboveCell000033102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102012) h)
        (by
          have h : ((childHH thetaAboveCell000033102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102013
        (by
          have h : ((childLL thetaAboveCell000033102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102013) h)
        (by
          have h : ((childLH thetaAboveCell000033102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102013) h)
        (by
          have h : ((childHL thetaAboveCell000033102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102013) h)
        (by
          have h : ((childHH thetaAboveCell000033102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102013) h))

theorem cover_subtree_afbc4e7a5775 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102020
        (by
          have h : ((childLL thetaAboveCell000033102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102020) h)
        (by
          have h : ((childLH thetaAboveCell000033102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102020) h)
        (by
          have h : ((childHL thetaAboveCell000033102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102020) h)
        (by
          have h : ((childHH thetaAboveCell000033102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102021
        (by
          have h : ((childLL thetaAboveCell000033102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102021) h)
        (by
          have h : ((childLH thetaAboveCell000033102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102021) h)
        (by
          have h : ((childHL thetaAboveCell000033102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102021) h)
        (by
          have h : ((childHH thetaAboveCell000033102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102022
        (by
          have h : ((childLL thetaAboveCell000033102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102022) h)
        (by
          have h : ((childLH thetaAboveCell000033102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102022) h)
        (by
          have h : ((childHL thetaAboveCell000033102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102022) h)
        (by
          have h : ((childHH thetaAboveCell000033102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102023
        (by
          have h : ((childLL thetaAboveCell000033102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102023) h)
        (by
          have h : ((childLH thetaAboveCell000033102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102023) h)
        (by
          have h : ((childHL thetaAboveCell000033102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102023) h)
        (by
          have h : ((childHH thetaAboveCell000033102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102023) h))

theorem cover_subtree_0885b8dd2e23 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102030
        (by
          have h : ((childLL thetaAboveCell000033102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102030) h)
        (by
          have h : ((childLH thetaAboveCell000033102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102030) h)
        (by
          have h : ((childHL thetaAboveCell000033102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102030) h)
        (by
          have h : ((childHH thetaAboveCell000033102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102031
        (by
          have h : ((childLL thetaAboveCell000033102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102031) h)
        (by
          have h : ((childLH thetaAboveCell000033102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102031) h)
        (by
          have h : ((childHL thetaAboveCell000033102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102031) h)
        (by
          have h : ((childHH thetaAboveCell000033102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102032
        (by
          have h : ((childLL thetaAboveCell000033102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102032) h)
        (by
          have h : ((childLH thetaAboveCell000033102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102032) h)
        (by
          have h : ((childHL thetaAboveCell000033102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102032) h)
        (by
          have h : ((childHH thetaAboveCell000033102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102033
        (by
          have h : ((childLL thetaAboveCell000033102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102033) h)
        (by
          have h : ((childLH thetaAboveCell000033102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102033) h)
        (by
          have h : ((childHL thetaAboveCell000033102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102033) h)
        (by
          have h : ((childHH thetaAboveCell000033102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102033) h))

theorem e24KC2ThetaAboveLeaf0000331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003310))
    cover_subtree_01b17a5cfced
    cover_subtree_26a3db88cf1e
    cover_subtree_afbc4e7a5775
    cover_subtree_0885b8dd2e23

end PartE
end GerverSofa

end

end

end
