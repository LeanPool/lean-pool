/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchAf2b60d8e2cf09a4`.
-/

@[expose] public section

noncomputable section


section

/-! E24KC6 explicit proof-producing certificate batch. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8ecd2c98f8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133110222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell11113311)))
/-- Subcell `111133110322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133110313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133110313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell11113311)))
/-- Subcell `111133111222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell11113311)))
/-- Subcell `111133111322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell11113311)))
/-- Subcell `111133111323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell11113311)))
/-- Subcell `111133111320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell11113311)))
/-- Subcell `111133111321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell11113311)))
/-- Subcell `111133111332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell11113311)))
/-- Subcell `111133111333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell11113311)))
/-- Subcell `111133111330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell11113311)))
/-- Subcell `111133111331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell11113311)))
/-- Subcell `111133112000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell11113311)))
/-- Subcell `111133112100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell11113311)))
/-- Subcell `111133112133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell11113311)))

end CertificateCells8ecd2c98f8

open CertificateCells8ecd2c98f8
theorem cover_subtree_d3f1948c7bb2 :
    adaptiveCoverCheck 6 thetaBelowCell111133110222 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110222
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133110222)
        (by
          have h : ((childLL (childLL thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133110222)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133110222)
        (by
          have h : ((childLL (childLH thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133110222)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133110222)
        (by
          have h : ((childLL (childHL thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133110222)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133110222)
        (by
          have h : ((childLL (childHH thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133110222)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133110222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133110222)) h))

theorem cover_subtree_06756667cdcb :
    adaptiveCoverCheck 6 thetaBelowCell111133110223 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110223
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133110223)
        (by
          have h : ((childLL (childLL thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133110223)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133110223)
        (by
          have h : ((childLL (childLH thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133110223)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133110223)
        (by
          have h : ((childLL (childHL thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133110223)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133110223)
        (by
          have h : ((childLL (childHH thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133110223)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133110223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133110223)) h))

theorem cover_subtree_5fd1a813f187 :
    adaptiveCoverCheck 7 (childHL (childHL (childLL thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL thetaBelowCell11113311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110220
        (by
          have h : ((childLL thetaBelowCell111133110220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110220) h)
        (by
          have h : ((childLH thetaBelowCell111133110220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110220) h)
        (by
          have h : ((childHL thetaBelowCell111133110220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133110220) h)
        (by
          have h : ((childHH thetaBelowCell111133110220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133110220) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110221
        (by
          have h : ((childLL thetaBelowCell111133110221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110221) h)
        (by
          have h : ((childLH thetaBelowCell111133110221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110221) h)
        (by
          have h : ((childHL thetaBelowCell111133110221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133110221) h)
        (by
          have h : ((childHH thetaBelowCell111133110221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133110221) h))
    cover_subtree_d3f1948c7bb2
    cover_subtree_06756667cdcb

theorem cover_subtree_985d36a8aada :
    adaptiveCoverCheck 6 thetaBelowCell111133110232 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110232
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133110232)
        (by
          have h : ((childLL (childLL thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133110232)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133110232)
        (by
          have h : ((childLL (childLH thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133110232)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133110232)
        (by
          have h : ((childLL (childHL thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133110232)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133110232)
        (by
          have h : ((childLL (childHH thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133110232)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133110232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133110232)) h))

theorem cover_subtree_91f684fb2a75 :
    adaptiveCoverCheck 6 thetaBelowCell111133110233 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110233
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133110233)
        (by
          have h : ((childLL (childLL thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133110233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133110233)
        (by
          have h : ((childLL (childLH thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133110233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133110233)
        (by
          have h : ((childLL (childHL thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133110233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133110233)
        (by
          have h : ((childLL (childHH thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133110233)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133110233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133110233)) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133110233))
            (by
              have h : ((childLL (childHH (childHH thetaBelowCell111133110233)))).rejected = true
                := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
                thetaBelowCell111133110233))) h)
            (by
              have h : ((childLH (childHH (childHH thetaBelowCell111133110233)))).rejected = true
                := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
                thetaBelowCell111133110233))) h)
            (by
              have h : ((childHL (childHH (childHH thetaBelowCell111133110233)))).rejected = true
                := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
                thetaBelowCell111133110233))) h)
            (by
              have h : ((childHH (childHH (childHH thetaBelowCell111133110233)))).rejected = true
                := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
                thetaBelowCell111133110233))) h)))

theorem cover_subtree_145b055d6873 :
    adaptiveCoverCheck 7 (childHH (childHL (childLL thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL thetaBelowCell11113311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110230
        (by
          have h : ((childLL thetaBelowCell111133110230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110230) h)
        (by
          have h : ((childLH thetaBelowCell111133110230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110230) h)
        (by
          have h : ((childHL thetaBelowCell111133110230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133110230) h)
        (by
          have h : ((childHH thetaBelowCell111133110230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133110230) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110231
        (by
          have h : ((childLL thetaBelowCell111133110231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110231) h)
        (by
          have h : ((childLH thetaBelowCell111133110231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110231) h)
        (by
          have h : ((childHL thetaBelowCell111133110231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133110231) h)
        (by
          have h : ((childHH thetaBelowCell111133110231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133110231) h))
    cover_subtree_985d36a8aada
    cover_subtree_91f684fb2a75

theorem cover_subtree_3ea9d3baa8d2 :
    adaptiveCoverCheck 8 (childHL (childLL thetaBelowCell11113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11113311))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133110200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110200 h)
        (by
          have h : (thetaBelowCell111133110201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110201 h)
        (by
          have h : (thetaBelowCell111133110202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110202 h)
        (by
          have h : (thetaBelowCell111133110203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133110210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110210 h)
        (by
          have h : (thetaBelowCell111133110211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110211 h)
        (by
          have h : (thetaBelowCell111133110212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110212 h)
        (by
          have h : (thetaBelowCell111133110213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110213 h))
    cover_subtree_5fd1a813f187
    cover_subtree_145b055d6873

theorem cover_subtree_2d2eae393440 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133110322) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133110322)
    (by
      have h : ((childLL (childHL thetaBelowCell111133110322))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL thetaBelowCell111133110322)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL thetaBelowCell111133110322))
        (by
          have h : ((childLL (childLH (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childLH (childLH (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL
            thetaBelowCell111133110322))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL thetaBelowCell111133110322))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHL
            thetaBelowCell111133110322))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133110322))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
            thetaBelowCell111133110322))) h))

theorem cover_subtree_4a90a1e8c08a :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133110322) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133110322)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133110322))
        (by
          have h : ((childLL (childLL (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childLH (childLL (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH
            thetaBelowCell111133110322))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133110322))
        (by
          have h : ((childLL (childLH (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childLH (childLH (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH
            thetaBelowCell111133110322))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133110322))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
            thetaBelowCell111133110322))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133110322))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
            thetaBelowCell111133110322))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell111133110322)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
            thetaBelowCell111133110322))) h))

theorem cover_subtree_179b6bbb140a :
    adaptiveCoverCheck 6 thetaBelowCell111133110322 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110322
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133110322)
        (by
          have h : ((childLL (childLL thetaBelowCell111133110322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133110322)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133110322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133110322)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133110322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133110322)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133110322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133110322)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133110322)
        (by
          have h : ((childLL (childLH thetaBelowCell111133110322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133110322)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133110322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133110322)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133110322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133110322)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133110322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133110322)) h))
    cover_subtree_2d2eae393440
    cover_subtree_4a90a1e8c08a

theorem cover_subtree_802a68149050 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133110323) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133110323)
    (by
      have h : ((childLL (childHL thetaBelowCell111133110323))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL thetaBelowCell111133110323)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell111133110323))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL thetaBelowCell111133110323)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL thetaBelowCell111133110323))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHL
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHL
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHL
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHL
            thetaBelowCell111133110323))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133110323))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
            thetaBelowCell111133110323))) h))

theorem cover_subtree_15d7407001b6 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133110323) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133110323)
    (by
      have h : ((childLL (childHH thetaBelowCell111133110323))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH thetaBelowCell111133110323)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell111133110323))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH thetaBelowCell111133110323)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133110323))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
            thetaBelowCell111133110323))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133110323))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
            thetaBelowCell111133110323))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell111133110323)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
            thetaBelowCell111133110323))) h))

theorem cover_subtree_6849ebb64c74 :
    adaptiveCoverCheck 6 thetaBelowCell111133110323 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110323
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133110323)
        (by
          have h : ((childLL (childLL thetaBelowCell111133110323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133110323)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133110323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133110323)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133110323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133110323)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133110323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133110323)) h))
    (by
      have h : ((childLH thetaBelowCell111133110323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110323) h)
    cover_subtree_802a68149050
    cover_subtree_15d7407001b6

theorem cover_subtree_4bd97887e2d4 :
    adaptiveCoverCheck 7 (childHL (childHH (childLL thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL thetaBelowCell11113311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110320
        (by
          have h : ((childLL thetaBelowCell111133110320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110320) h)
        (by
          have h : ((childLH thetaBelowCell111133110320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110320) h)
        (by
          have h : ((childHL thetaBelowCell111133110320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133110320) h)
        (by
          have h : ((childHH thetaBelowCell111133110320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133110320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110321
        (by
          have h : ((childLL thetaBelowCell111133110321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110321) h)
        (by
          have h : ((childLH thetaBelowCell111133110321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110321) h)
        (by
          have h : ((childHL thetaBelowCell111133110321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133110321) h)
        (by
          have h : ((childHH thetaBelowCell111133110321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133110321) h))
    cover_subtree_179b6bbb140a
    cover_subtree_6849ebb64c74

theorem cover_subtree_63bf927d197e :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133110332) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133110332)
    (by
      have h : ((childLL (childHL thetaBelowCell111133110332))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL thetaBelowCell111133110332)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell111133110332))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL thetaBelowCell111133110332)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL thetaBelowCell111133110332))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHL
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHL
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHL
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHL
            thetaBelowCell111133110332))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133110332))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
            thetaBelowCell111133110332))) h))

theorem cover_subtree_4b23bc69c953 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133110332) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133110332)
    (by
      have h : ((childLL (childHH thetaBelowCell111133110332))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH thetaBelowCell111133110332)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell111133110332))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH thetaBelowCell111133110332)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133110332))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
            thetaBelowCell111133110332))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133110332))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
            thetaBelowCell111133110332))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell111133110332)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
            thetaBelowCell111133110332))) h))

theorem cover_subtree_b2776b022cdc :
    adaptiveCoverCheck 6 thetaBelowCell111133110332 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110332
    (by
      have h : ((childLL thetaBelowCell111133110332)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110332) h)
    (by
      have h : ((childLH thetaBelowCell111133110332)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110332) h)
    cover_subtree_63bf927d197e
    cover_subtree_4b23bc69c953

theorem cover_subtree_273cf6356f9d :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133110333) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133110333)
    (by
      have h : ((childLL (childHL thetaBelowCell111133110333))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL thetaBelowCell111133110333)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell111133110333))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL thetaBelowCell111133110333)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL thetaBelowCell111133110333))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHL
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHL
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHL
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHL
            thetaBelowCell111133110333))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133110333))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
            thetaBelowCell111133110333))) h))

theorem cover_subtree_27ddb3080e9d :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133110333) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133110333)
    (by
      have h : ((childLL (childHH thetaBelowCell111133110333))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH thetaBelowCell111133110333)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell111133110333))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH thetaBelowCell111133110333)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133110333))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
            thetaBelowCell111133110333))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133110333))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
            thetaBelowCell111133110333))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell111133110333)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
            thetaBelowCell111133110333))) h))

theorem cover_subtree_27a44a78bf0e :
    adaptiveCoverCheck 6 thetaBelowCell111133110333 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110333
    (by
      have h : ((childLL thetaBelowCell111133110333)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110333) h)
    (by
      have h : ((childLH thetaBelowCell111133110333)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110333) h)
    cover_subtree_273cf6356f9d
    cover_subtree_27ddb3080e9d

theorem cover_subtree_0fe512b8a712 :
    adaptiveCoverCheck 7 (childHH (childHH (childLL thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL thetaBelowCell11113311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133110330
        (by
          have h : ((childLL thetaBelowCell111133110330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133110330) h)
        (by
          have h : ((childLH thetaBelowCell111133110330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133110330) h)
        (by
          have h : ((childHL thetaBelowCell111133110330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133110330) h)
        (by
          have h : ((childHH thetaBelowCell111133110330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133110330) h))
    (by
      have h : (thetaBelowCell111133110331).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110331 h)
    cover_subtree_b2776b022cdc
    cover_subtree_27a44a78bf0e

theorem cover_subtree_780d3c38d99a :
    adaptiveCoverCheck 8 (childHH (childLL thetaBelowCell11113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11113311))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133110300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110300 h)
        (by
          have h : (thetaBelowCell111133110301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110301 h)
        (by
          have h : (thetaBelowCell111133110302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110302 h)
        (by
          have h : (thetaBelowCell111133110303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133110310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110310 h)
        (by
          have h : (thetaBelowCell111133110311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110311 h)
        (by
          have h : (thetaBelowCell111133110312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110312 h)
        (by
          have h : (thetaBelowCell111133110313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133110313 h))
    cover_subtree_4bd97887e2d4
    cover_subtree_0fe512b8a712

theorem e24KC2ThetaBelowLeaf111133110 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113311)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11113311))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11113311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11113311))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11113311))) h))
    cover_subtree_3ea9d3baa8d2
    cover_subtree_780d3c38d99a
theorem cover_subtree_789cd4100198 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133111222) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133111222)
    (by
      have h : ((childLL (childHL thetaBelowCell111133111222))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL thetaBelowCell111133111222)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell111133111222))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL thetaBelowCell111133111222)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL thetaBelowCell111133111222))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHL
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHL
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHL
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHL
            thetaBelowCell111133111222))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133111222))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
            thetaBelowCell111133111222))) h))

theorem cover_subtree_c3bc65d3adac :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133111222) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133111222)
    (by
      have h : ((childLL (childHH thetaBelowCell111133111222))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH thetaBelowCell111133111222)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell111133111222))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH thetaBelowCell111133111222)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133111222))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
            thetaBelowCell111133111222))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133111222))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
            thetaBelowCell111133111222))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell111133111222)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
            thetaBelowCell111133111222))) h))

theorem cover_subtree_006e01dadc14 :
    adaptiveCoverCheck 6 thetaBelowCell111133111222 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133111222
    (by
      have h : ((childLL thetaBelowCell111133111222)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133111222) h)
    (by
      have h : ((childLH thetaBelowCell111133111222)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133111222) h)
    cover_subtree_789cd4100198
    cover_subtree_c3bc65d3adac

theorem cover_subtree_15ffb840ba9a :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133111223) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133111223)
    (by
      have h : ((childLL (childHL thetaBelowCell111133111223))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL thetaBelowCell111133111223)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell111133111223))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL thetaBelowCell111133111223)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL thetaBelowCell111133111223))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHL
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHL
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHL
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHL
            thetaBelowCell111133111223))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133111223))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
            thetaBelowCell111133111223))) h))

theorem cover_subtree_f79e20abb6dd :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133111223) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133111223)
    (by
      have h : ((childLL (childHH thetaBelowCell111133111223))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH thetaBelowCell111133111223)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell111133111223))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH thetaBelowCell111133111223)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133111223))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
            thetaBelowCell111133111223))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133111223))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
            thetaBelowCell111133111223))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell111133111223)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
            thetaBelowCell111133111223))) h))

theorem cover_subtree_c67dbdb52005 :
    adaptiveCoverCheck 6 thetaBelowCell111133111223 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133111223
    (by
      have h : ((childLL thetaBelowCell111133111223)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133111223) h)
    (by
      have h : ((childLH thetaBelowCell111133111223)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133111223) h)
    cover_subtree_15ffb840ba9a
    cover_subtree_f79e20abb6dd

theorem cover_subtree_7319345fe5a3 :
    adaptiveCoverCheck 7 (childHL (childHL (childLH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH thetaBelowCell11113311)))
    (by
      have h : (thetaBelowCell111133111220).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111220 h)
    (by
      have h : (thetaBelowCell111133111221).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111221 h)
    cover_subtree_006e01dadc14
    cover_subtree_c67dbdb52005

theorem cover_subtree_95410d7d0fe9 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133111232) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133111232)
    (by
      have h : ((childLL (childHL thetaBelowCell111133111232))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL thetaBelowCell111133111232)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell111133111232))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL thetaBelowCell111133111232)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL thetaBelowCell111133111232))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell111133111232)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHL
            thetaBelowCell111133111232))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell111133111232)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHL
            thetaBelowCell111133111232))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell111133111232)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHL
            thetaBelowCell111133111232))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell111133111232)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHL
            thetaBelowCell111133111232))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133111232))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell111133111232)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
            thetaBelowCell111133111232))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell111133111232)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
            thetaBelowCell111133111232))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell111133111232)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
            thetaBelowCell111133111232))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell111133111232)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
            thetaBelowCell111133111232))) h))

theorem cover_subtree_bb5d3c6632a7 :
    adaptiveCoverCheck 6 thetaBelowCell111133111232 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133111232
    (by
      have h : ((childLL thetaBelowCell111133111232)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133111232) h)
    (by
      have h : ((childLH thetaBelowCell111133111232)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133111232) h)
    cover_subtree_95410d7d0fe9
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133111232)
        (by
          have h : ((childLL (childHH thetaBelowCell111133111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133111232)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133111232)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133111232)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133111232)) h))

theorem cover_subtree_36f6a3ec0dcf :
    adaptiveCoverCheck 6 thetaBelowCell111133111233 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133111233
    (by
      have h : ((childLL thetaBelowCell111133111233)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133111233) h)
    (by
      have h : ((childLH thetaBelowCell111133111233)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133111233) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133111233)
        (by
          have h : ((childLL (childHL thetaBelowCell111133111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133111233)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133111233)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133111233)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133111233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133111233)
        (by
          have h : ((childLL (childHH thetaBelowCell111133111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133111233)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133111233)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133111233)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133111233)) h))

theorem cover_subtree_51a12797f9e1 :
    adaptiveCoverCheck 7 (childHH (childHL (childLH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH thetaBelowCell11113311)))
    (by
      have h : (thetaBelowCell111133111230).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111230 h)
    (by
      have h : (thetaBelowCell111133111231).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111231 h)
    cover_subtree_bb5d3c6632a7
    cover_subtree_36f6a3ec0dcf

theorem cover_subtree_8ababed519f4 :
    adaptiveCoverCheck 8 (childHL (childLH thetaBelowCell11113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11113311))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133111200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111200 h)
        (by
          have h : (thetaBelowCell111133111201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111201 h)
        (by
          have h : (thetaBelowCell111133111202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111202 h)
        (by
          have h : (thetaBelowCell111133111203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111203 h))
    (by
      have h : ((childLH (childHL (childLH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH
        thetaBelowCell11113311))) h)
    cover_subtree_7319345fe5a3
    cover_subtree_51a12797f9e1

theorem cover_subtree_b8b0e3b2827e :
    adaptiveCoverCheck 6 thetaBelowCell111133111322 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133111322
    (by
      have h : ((childLL thetaBelowCell111133111322)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133111322) h)
    (by
      have h : ((childLH thetaBelowCell111133111322)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133111322) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133111322)
        (by
          have h : ((childLL (childHL thetaBelowCell111133111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133111322)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133111322)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133111322)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133111322)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133111322)
        (by
          have h : ((childLL (childHH thetaBelowCell111133111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133111322)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133111322)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133111322)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133111322)) h))

theorem cover_subtree_2989b06dc516 :
    adaptiveCoverCheck 6 thetaBelowCell111133111323 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133111323
    (by
      have h : ((childLL thetaBelowCell111133111323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133111323) h)
    (by
      have h : ((childLH thetaBelowCell111133111323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133111323) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133111323)
        (by
          have h : ((childLL (childHL thetaBelowCell111133111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133111323)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133111323)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133111323)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133111323)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133111323)
        (by
          have h : ((childLL (childHH thetaBelowCell111133111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133111323)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133111323)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133111323)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133111323)) h))

theorem cover_subtree_bf01e4b37001 :
    adaptiveCoverCheck 7 (childHL (childHH (childLH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH thetaBelowCell11113311)))
    (by
      have h : (thetaBelowCell111133111320).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111320 h)
    (by
      have h : (thetaBelowCell111133111321).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111321 h)
    cover_subtree_b8b0e3b2827e
    cover_subtree_2989b06dc516

theorem cover_subtree_730eb8da47c4 :
    adaptiveCoverCheck 6 thetaBelowCell111133111332 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133111332
    (by
      have h : ((childLL thetaBelowCell111133111332)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133111332) h)
    (by
      have h : ((childLH thetaBelowCell111133111332)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133111332) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133111332)
        (by
          have h : ((childLL (childHL thetaBelowCell111133111332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133111332)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133111332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133111332)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133111332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133111332)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133111332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133111332)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133111332)
        (by
          have h : ((childLL (childHH thetaBelowCell111133111332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133111332)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133111332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133111332)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133111332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133111332)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133111332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133111332)) h))

theorem cover_subtree_1841de2ff0e1 :
    adaptiveCoverCheck 6 thetaBelowCell111133111333 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133111333
    (by
      have h : ((childLL thetaBelowCell111133111333)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133111333) h)
    (by
      have h : ((childLH thetaBelowCell111133111333)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133111333) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133111333)
        (by
          have h : ((childLL (childHL thetaBelowCell111133111333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133111333)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133111333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133111333)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133111333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133111333)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133111333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133111333)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133111333)
        (by
          have h : ((childLL (childHH thetaBelowCell111133111333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133111333)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133111333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133111333)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133111333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133111333)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133111333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133111333)) h))

theorem cover_subtree_245b6882ed3e :
    adaptiveCoverCheck 7 (childHH (childHH (childLH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH thetaBelowCell11113311)))
    (by
      have h : (thetaBelowCell111133111330).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111330 h)
    (by
      have h : (thetaBelowCell111133111331).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133111331 h)
    cover_subtree_730eb8da47c4
    cover_subtree_1841de2ff0e1

theorem cover_subtree_a132a8d74d97 :
    adaptiveCoverCheck 8 (childHH (childLH thetaBelowCell11113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11113311))
    (by
      have h : ((childLL (childHH (childLH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH
        thetaBelowCell11113311))) h)
    (by
      have h : ((childLH (childHH (childLH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH
        thetaBelowCell11113311))) h)
    cover_subtree_bf01e4b37001
    cover_subtree_245b6882ed3e

theorem e24KC2ThetaBelowLeaf111133111 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113311)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11113311))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11113311))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11113311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11113311))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11113311))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11113311))) h))
    cover_subtree_8ababed519f4
    cover_subtree_a132a8d74d97
theorem cover_subtree_d86d6d397d37 :
    adaptiveCoverCheck 6 thetaBelowCell111133112000 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112000
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133112000)
        (by
          have h : ((childLL (childLL thetaBelowCell111133112000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133112000)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133112000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133112000)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133112000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133112000)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133112000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133112000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133112000)
        (by
          have h : ((childLL (childLH thetaBelowCell111133112000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133112000)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133112000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133112000)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133112000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133112000)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133112000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133112000)) h))
    (by
      have h : ((childHL thetaBelowCell111133112000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112000) h)
    (by
      have h : ((childHH thetaBelowCell111133112000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112000) h)

theorem cover_subtree_6aa6edf26d6b :
    adaptiveCoverCheck 6 thetaBelowCell111133112001 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112001
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133112001)
        (by
          have h : ((childLL (childLL thetaBelowCell111133112001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133112001)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133112001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133112001)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133112001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133112001)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133112001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133112001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133112001)
        (by
          have h : ((childLL (childLH thetaBelowCell111133112001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133112001)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133112001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133112001)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133112001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133112001)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133112001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133112001)) h))
    (by
      have h : ((childHL thetaBelowCell111133112001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112001) h)
    (by
      have h : ((childHH thetaBelowCell111133112001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112001) h)

theorem cover_subtree_08f0ea41225e :
    adaptiveCoverCheck 7 (childLL (childLL (childHL thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHL thetaBelowCell11113311)))
    cover_subtree_d86d6d397d37
    cover_subtree_6aa6edf26d6b
    (by
      have h : (thetaBelowCell111133112002).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112002 h)
    (by
      have h : (thetaBelowCell111133112003).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112003 h)

theorem cover_subtree_9a3060df2fad :
    adaptiveCoverCheck 6 thetaBelowCell111133112010 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112010
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133112010)
        (by
          have h : ((childLL (childLL thetaBelowCell111133112010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133112010)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133112010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133112010)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133112010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133112010)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133112010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133112010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133112010)
        (by
          have h : ((childLL (childLH thetaBelowCell111133112010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133112010)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133112010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133112010)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133112010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133112010)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133112010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133112010)) h))
    (by
      have h : ((childHL thetaBelowCell111133112010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112010) h)
    (by
      have h : ((childHH thetaBelowCell111133112010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112010) h)

theorem cover_subtree_2515da0e05d0 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133112011) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133112011)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133112011))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133112011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133112011))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133112011))) h))
    (by
      have h : ((childHL (childLL thetaBelowCell111133112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL thetaBelowCell111133112011)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell111133112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL thetaBelowCell111133112011)) h)

theorem cover_subtree_2e5826939a0b :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133112011) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133112011)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133112011))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133112011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133112011))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133112011))) h))
    (by
      have h : ((childHL (childLH thetaBelowCell111133112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH thetaBelowCell111133112011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133112011))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLH
            thetaBelowCell111133112011))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell111133112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLH
            thetaBelowCell111133112011))) h))

theorem cover_subtree_9e7e8b4def5a :
    adaptiveCoverCheck 6 thetaBelowCell111133112011 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112011
    cover_subtree_2515da0e05d0
    cover_subtree_2e5826939a0b
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133112011)
        (by
          have h : ((childLL (childHL thetaBelowCell111133112011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133112011)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133112011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133112011)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133112011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133112011)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133112011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133112011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133112011)
        (by
          have h : ((childLL (childHH thetaBelowCell111133112011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133112011)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133112011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133112011)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133112011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133112011)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133112011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133112011)) h))

theorem cover_subtree_6ec9728983f6 :
    adaptiveCoverCheck 7 (childLH (childLL (childHL thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHL thetaBelowCell11113311)))
    cover_subtree_9a3060df2fad
    cover_subtree_9e7e8b4def5a
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112012
        (by
          have h : ((childLL thetaBelowCell111133112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133112012) h)
        (by
          have h : ((childLH thetaBelowCell111133112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133112012) h)
        (by
          have h : ((childHL thetaBelowCell111133112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112012) h)
        (by
          have h : ((childHH thetaBelowCell111133112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112013
        (by
          have h : ((childLL thetaBelowCell111133112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133112013) h)
        (by
          have h : ((childLH thetaBelowCell111133112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133112013) h)
        (by
          have h : ((childHL thetaBelowCell111133112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112013) h)
        (by
          have h : ((childHH thetaBelowCell111133112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112013) h))

theorem cover_subtree_35cd51a2309c :
    adaptiveCoverCheck 8 (childLL (childHL thetaBelowCell11113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL thetaBelowCell11113311))
    cover_subtree_08f0ea41225e
    cover_subtree_6ec9728983f6
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childHL
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112020 h)
        (by
          have h : (thetaBelowCell111133112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112021 h)
        (by
          have h : (thetaBelowCell111133112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112022 h)
        (by
          have h : (thetaBelowCell111133112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childHL
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112030 h)
        (by
          have h : (thetaBelowCell111133112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112031 h)
        (by
          have h : (thetaBelowCell111133112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112032 h)
        (by
          have h : (thetaBelowCell111133112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112033 h))

theorem cover_subtree_15005e137c79 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133112100) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133112100)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133112100))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133112100))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133112100))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLL
            thetaBelowCell111133112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133112100))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLL
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLL
            thetaBelowCell111133112100))) h))

theorem cover_subtree_28298b1a6476 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133112100) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133112100)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133112100))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133112100))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133112100))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLH
            thetaBelowCell111133112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133112100))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLH
            thetaBelowCell111133112100))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell111133112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLH
            thetaBelowCell111133112100))) h))

theorem cover_subtree_dd3b58e15058 :
    adaptiveCoverCheck 6 thetaBelowCell111133112100 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112100
    cover_subtree_15005e137c79
    cover_subtree_28298b1a6476
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133112100)
        (by
          have h : ((childLL (childHL thetaBelowCell111133112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133112100)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133112100)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133112100)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133112100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133112100)
        (by
          have h : ((childLL (childHH thetaBelowCell111133112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133112100)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133112100)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133112100)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133112100)) h))

theorem cover_subtree_e1ad3991ba4f :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133112101) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133112101)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133112101))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133112101))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133112101))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLL
            thetaBelowCell111133112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133112101))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLL
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLL
            thetaBelowCell111133112101))) h))

theorem cover_subtree_222381d65095 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133112101) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133112101)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133112101))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133112101))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133112101))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLH
            thetaBelowCell111133112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133112101))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLH
            thetaBelowCell111133112101))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell111133112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLH
            thetaBelowCell111133112101))) h))

theorem cover_subtree_a500ccb0f9dd :
    adaptiveCoverCheck 6 thetaBelowCell111133112101 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112101
    cover_subtree_e1ad3991ba4f
    cover_subtree_222381d65095
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133112101)
        (by
          have h : ((childLL (childHL thetaBelowCell111133112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133112101)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133112101)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133112101)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133112101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133112101)
        (by
          have h : ((childLL (childHH thetaBelowCell111133112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133112101)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133112101)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133112101)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133112101)) h))

theorem cover_subtree_b97026ab0ee7 :
    adaptiveCoverCheck 7 (childLL (childLH (childHL thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHL thetaBelowCell11113311)))
    cover_subtree_dd3b58e15058
    cover_subtree_a500ccb0f9dd
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112102
        (by
          have h : ((childLL thetaBelowCell111133112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133112102) h)
        (by
          have h : ((childLH thetaBelowCell111133112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133112102) h)
        (by
          have h : ((childHL thetaBelowCell111133112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112102) h)
        (by
          have h : ((childHH thetaBelowCell111133112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112103
        (by
          have h : ((childLL thetaBelowCell111133112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133112103) h)
        (by
          have h : ((childLH thetaBelowCell111133112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133112103) h)
        (by
          have h : ((childHL thetaBelowCell111133112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112103) h)
        (by
          have h : ((childHH thetaBelowCell111133112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112103) h))

theorem cover_subtree_0942b83515e8 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133112110) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133112110)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133112110))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133112110))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133112110))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLL
            thetaBelowCell111133112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133112110))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLL
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLL
            thetaBelowCell111133112110))) h))

theorem cover_subtree_4ccf6d139a48 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133112110) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133112110)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133112110))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133112110))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133112110))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLH
            thetaBelowCell111133112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133112110))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLH
            thetaBelowCell111133112110))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell111133112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLH
            thetaBelowCell111133112110))) h))

theorem cover_subtree_b6335e66944c :
    adaptiveCoverCheck 6 thetaBelowCell111133112110 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112110
    cover_subtree_0942b83515e8
    cover_subtree_4ccf6d139a48
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133112110)
        (by
          have h : ((childLL (childHL thetaBelowCell111133112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133112110)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133112110)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133112110)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133112110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133112110)
        (by
          have h : ((childLL (childHH thetaBelowCell111133112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133112110)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133112110)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133112110)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133112110)) h))

theorem cover_subtree_964421ffff09 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133112111) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133112111)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133112111))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133112111))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133112111))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLL
            thetaBelowCell111133112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133112111))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLL
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLL
            thetaBelowCell111133112111))) h))

theorem cover_subtree_d60f6638c35c :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133112111) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133112111)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133112111))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133112111))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133112111))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLH
            thetaBelowCell111133112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133112111))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLH
            thetaBelowCell111133112111))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell111133112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLH
            thetaBelowCell111133112111))) h))

theorem cover_subtree_fd996b69dc6a :
    adaptiveCoverCheck 6 thetaBelowCell111133112111 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112111
    cover_subtree_964421ffff09
    cover_subtree_d60f6638c35c
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133112111)
        (by
          have h : ((childLL (childHL thetaBelowCell111133112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133112111)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133112111)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133112111)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133112111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133112111)
        (by
          have h : ((childLL (childHH thetaBelowCell111133112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133112111)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133112111)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133112111)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133112111)) h))

theorem cover_subtree_4fddc783c766 :
    adaptiveCoverCheck 7 (childLH (childLH (childHL thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHL thetaBelowCell11113311)))
    cover_subtree_b6335e66944c
    cover_subtree_fd996b69dc6a
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112112
        (by
          have h : ((childLL thetaBelowCell111133112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133112112) h)
        (by
          have h : ((childLH thetaBelowCell111133112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133112112) h)
        (by
          have h : ((childHL thetaBelowCell111133112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112112) h)
        (by
          have h : ((childHH thetaBelowCell111133112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133112113
        (by
          have h : ((childLL thetaBelowCell111133112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133112113) h)
        (by
          have h : ((childLH thetaBelowCell111133112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133112113) h)
        (by
          have h : ((childHL thetaBelowCell111133112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133112113) h)
        (by
          have h : ((childHH thetaBelowCell111133112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133112113) h))

theorem cover_subtree_06a38a993bbb :
    adaptiveCoverCheck 8 (childLH (childHL thetaBelowCell11113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL thetaBelowCell11113311))
    cover_subtree_b97026ab0ee7
    cover_subtree_4fddc783c766
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childHL
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112120 h)
        (by
          have h : (thetaBelowCell111133112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112121 h)
        (by
          have h : (thetaBelowCell111133112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112122 h)
        (by
          have h : (thetaBelowCell111133112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childHL
        thetaBelowCell11113311)))
        (by
          have h : (thetaBelowCell111133112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112130 h)
        (by
          have h : (thetaBelowCell111133112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112131 h)
        (by
          have h : (thetaBelowCell111133112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112132 h)
        (by
          have h : (thetaBelowCell111133112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133112133 h))

theorem e24KC2ThetaBelowLeaf111133112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113311)
    cover_subtree_35cd51a2309c
    cover_subtree_06a38a993bbb
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL thetaBelowCell11113311))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL
            thetaBelowCell11113311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL thetaBelowCell11113311))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL
            thetaBelowCell11113311))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell11113311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL
            thetaBelowCell11113311))) h))

end PartE
end GerverSofa

end

end

end
