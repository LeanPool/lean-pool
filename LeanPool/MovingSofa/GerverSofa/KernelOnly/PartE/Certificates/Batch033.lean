/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch032





/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6R4Subtree7c075da8e9f0577b`.
* `KernelOnly.PartE.E24KC6R4Subtree7e83efce8bd8caa9`.
* `KernelOnly.PartE.E24KC6R4Join57ced70670a400e2`.
* `KernelOnly.PartE.E24KC6R4Subtree81ebe3f900bc76a5`.
* `KernelOnly.PartE.E24KC6R4Subtree84bebec26b36007b`.
* `KernelOnly.PartE.E24KC6R4Subtree879f3ccc81ca9b24`.
* `KernelOnly.PartE.E24KC6R4Subtree88f80fd4db374a2d`.
* `KernelOnly.PartE.E24KC6R4Subtree8921da6a3153d018`.
* `KernelOnly.PartE.E24KC6R4Subtree89badd31312e459d`.
* `KernelOnly.PartE.E24KC6R4Subtree8b6172e52c41dded`.
* `KernelOnly.PartE.E24KC6R4Join0f0434a94ae699a2`.
-/

@[expose] public section

noncomputable section


section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsefec3b1324

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))
/-- Subcell `1111331131111222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113111)))
/-- Subcell `1111331131111333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113111)))

end CertificateCellsefec3b1324

open CertificateCellsefec3b1324
theorem cover_subtree_7aa3d52e724a :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111222 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111222
    (by
      have h : ((childLL thetaBelowCell1111331131111222)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111222) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111222)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111222) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111222)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111222)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111222)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111222)) h))

theorem cover_subtree_818c6b64504a :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111223 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111223
    (by
      have h : ((childLL thetaBelowCell1111331131111223)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111223) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111223)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111223) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111223)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111223)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111223)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111223)) h))

theorem cover_subtree_75546d36bae0 :
    adaptiveCoverCheck 3 (childHL (childHL (childLH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131111220).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111220 h)
    (by
      have h : (thetaBelowCell1111331131111221).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111221 h)
    cover_subtree_7aa3d52e724a
    cover_subtree_818c6b64504a

theorem cover_subtree_38aeeec8d754 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111232 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111232
    (by
      have h : ((childLL thetaBelowCell1111331131111232)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111232) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111232)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111232) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111232)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111232)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111232)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111232)) h))

theorem cover_subtree_7653e3da7d41 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111233 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111233
    (by
      have h : ((childLL thetaBelowCell1111331131111233)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111233) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111233)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111233) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111233)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111233)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111233)) h))

theorem cover_subtree_c48c3d0e1082 :
    adaptiveCoverCheck 3 (childHH (childHL (childLH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131111230).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111230 h)
    (by
      have h : (thetaBelowCell1111331131111231).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111231 h)
    cover_subtree_38aeeec8d754
    cover_subtree_7653e3da7d41

theorem cover_subtree_850575b22b27 :
    adaptiveCoverCheck 4 (childHL (childLH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHL (childLH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHL (childLH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH
        thetaBelowCell111133113111))) h)
    cover_subtree_75546d36bae0
    cover_subtree_c48c3d0e1082

theorem cover_subtree_8b97f2fa7857 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111322 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111322
    (by
      have h : ((childLL thetaBelowCell1111331131111322)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111322) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111322)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111322) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111322)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111322)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111322)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111322)) h))

theorem cover_subtree_4e37d42ba06c :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111323 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111323
    (by
      have h : ((childLL thetaBelowCell1111331131111323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111323) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111323) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111323)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111323)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111323)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111323)) h))

theorem cover_subtree_27a9e6ae3bf9 :
    adaptiveCoverCheck 3 (childHL (childHH (childLH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131111320).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111320 h)
    (by
      have h : (thetaBelowCell1111331131111321).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111321 h)
    cover_subtree_8b97f2fa7857
    cover_subtree_4e37d42ba06c

theorem cover_subtree_73b432883d7f :
    adaptiveCoverCheck 3 (childHH (childHH (childLH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131111330).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111330 h)
    (by
      have h : (thetaBelowCell1111331131111331).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111331 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111332
        (by
          have h : ((childLL thetaBelowCell1111331131111332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111332) h)
        (by
          have h : ((childLH thetaBelowCell1111331131111332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111332) h)
        (by
          have h : ((childHL thetaBelowCell1111331131111332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131111332) h)
        (by
          have h : ((childHH thetaBelowCell1111331131111332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131111332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111333
        (by
          have h : ((childLL thetaBelowCell1111331131111333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111333) h)
        (by
          have h : ((childLH thetaBelowCell1111331131111333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111333) h)
        (by
          have h : ((childHL thetaBelowCell1111331131111333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131111333) h)
        (by
          have h : ((childHH thetaBelowCell1111331131111333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131111333) h))

theorem cover_subtree_cff1fffcbf04 :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHH (childLH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHH (childLH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
        thetaBelowCell111133113111))) h)
    cover_subtree_27a9e6ae3bf9
    cover_subtree_73b432883d7f

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c1 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113111) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113111)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113111))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133113111))) h))
    (by
      have h : ((childLH (childLH thetaBelowCell111133113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH thetaBelowCell111133113111)) h)
    cover_subtree_850575b22b27
    cover_subtree_cff1fffcbf04

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells11cd3db1c7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113311)))
/-- Subcell `1111331131103000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell111133113110)))
/-- Subcell `1111331131103133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell111133113110)))

end CertificateCells11cd3db1c7

open CertificateCells11cd3db1c7
theorem cover_subtree_36a7bfb19453 :
    adaptiveCoverCheck 3 (childLL (childLL (childHH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103000
        (by
          have h : ((childLL thetaBelowCell1111331131103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103000) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103000) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103000) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103001
        (by
          have h : ((childLL thetaBelowCell1111331131103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103001) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103001) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103001) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103001) h))
    (by
      have h : (thetaBelowCell1111331131103002).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103002 h)
    (by
      have h : (thetaBelowCell1111331131103003).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103003 h)

theorem cover_subtree_05a08e0bea5f :
    adaptiveCoverCheck 3 (childLH (childLL (childHH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103010
        (by
          have h : ((childLL thetaBelowCell1111331131103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103010) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103010) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103010) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103011
        (by
          have h : ((childLL thetaBelowCell1111331131103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103011) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103011) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103011) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103011) h))
    (by
      have h : (thetaBelowCell1111331131103012).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103012 h)
    (by
      have h : (thetaBelowCell1111331131103013).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103013 h)

theorem cover_subtree_e2abbc5cba3c :
    adaptiveCoverCheck 4 (childLL (childHH thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133113110))
    cover_subtree_36a7bfb19453
    cover_subtree_05a08e0bea5f
    (by
      have h : ((childHL (childLL (childHH thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH
        thetaBelowCell111133113110))) h)
    (by
      have h : ((childHH (childLL (childHH thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH
        thetaBelowCell111133113110))) h)

theorem cover_subtree_09ec3c616243 :
    adaptiveCoverCheck 3 (childLL (childLH (childHH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103100
        (by
          have h : ((childLL thetaBelowCell1111331131103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103100) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103100) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103100) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103101
        (by
          have h : ((childLL thetaBelowCell1111331131103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103101) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103101) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103101) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103101) h))
    (by
      have h : (thetaBelowCell1111331131103102).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103102 h)
    (by
      have h : (thetaBelowCell1111331131103103).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103103 h)

theorem cover_subtree_6c69a3f38b7c :
    adaptiveCoverCheck 3 (childLH (childLH (childHH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103110
        (by
          have h : ((childLL thetaBelowCell1111331131103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103110) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103110) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103110) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103111
        (by
          have h : ((childLL thetaBelowCell1111331131103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103111) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103111) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103111) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103111) h))
    (by
      have h : (thetaBelowCell1111331131103112).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103112 h)
    (by
      have h : (thetaBelowCell1111331131103113).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103113 h)

theorem cover_subtree_5b1de072a154 :
    adaptiveCoverCheck 4 (childLH (childHH thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133113110))
    cover_subtree_09ec3c616243
    cover_subtree_6c69a3f38b7c
    (by
      have h : ((childHL (childLH (childHH thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH
        thetaBelowCell111133113110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childHH
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103130 h)
        (by
          have h : (thetaBelowCell1111331131103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103131 h)
        (by
          have h : (thetaBelowCell1111331131103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103132 h)
        (by
          have h : (thetaBelowCell1111331131103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103133 h))

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c3 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113110)
    cover_subtree_e2abbc5cba3c
    cover_subtree_5b1de072a154
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133113110))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
            thetaBelowCell111133113110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133113110))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
            thetaBelowCell111133113110))) h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse82c2dced4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113311)))

end CertificateCellse82c2dced4

open CertificateCellse82c2dced4

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c0 :
    adaptiveCoverCheck 6 thetaBelowCell111133113110 = true :=
  adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113110
    e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c0 e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c1
      e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c2 e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7a1b24c2da

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133113101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113311)))
/-- Subcell `1111331131011220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell111133113101)))
/-- Subcell `1111331131011313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell111133113101)))

end CertificateCells7a1b24c2da

open CertificateCells7a1b24c2da
theorem cover_subtree_9615f1192754 :
    adaptiveCoverCheck 3 (childHL (childHL (childLH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH
    thetaBelowCell111133113101)))
    (by
      have h : (thetaBelowCell1111331131011220).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011220 h)
    (by
      have h : (thetaBelowCell1111331131011221).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011221 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011222
        (by
          have h : ((childLL thetaBelowCell1111331131011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011222) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011222) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011222) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011223
        (by
          have h : ((childLL thetaBelowCell1111331131011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011223) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011223) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011223) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011223) h))

theorem cover_subtree_1f726b3116b0 :
    adaptiveCoverCheck 3 (childHH (childHL (childLH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH
    thetaBelowCell111133113101)))
    (by
      have h : (thetaBelowCell1111331131011230).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011230 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011231
        (by
          have h : ((childLL thetaBelowCell1111331131011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011231) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011231) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011231) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011232
        (by
          have h : ((childLL thetaBelowCell1111331131011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011232) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011232) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011232) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011233
        (by
          have h : ((childLL thetaBelowCell1111331131011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011233) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011233) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011233) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011233) h))

theorem cover_subtree_cac2e3b1401d :
    adaptiveCoverCheck 4 (childHL (childLH thetaBelowCell111133113101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113101))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131011200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011200 h)
        (by
          have h : (thetaBelowCell1111331131011201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011201 h)
        (by
          have h : (thetaBelowCell1111331131011202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011202 h)
        (by
          have h : (thetaBelowCell1111331131011203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131011210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011210 h)
        (by
          have h : (thetaBelowCell1111331131011211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011211 h)
        (by
          have h : (thetaBelowCell1111331131011212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011212 h)
        (by
          have h : (thetaBelowCell1111331131011213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011213 h))
    cover_subtree_9615f1192754
    cover_subtree_1f726b3116b0

theorem cover_subtree_4f3cdd0c257d :
    adaptiveCoverCheck 3 (childHL (childHH (childLH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
    thetaBelowCell111133113101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011320
        (by
          have h : ((childLL thetaBelowCell1111331131011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011320) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011320) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011320) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011321
        (by
          have h : ((childLL thetaBelowCell1111331131011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011321) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011321) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011321) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011321) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011322
        (by
          have h : ((childLL thetaBelowCell1111331131011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011322) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011322) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011322) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011322) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011323
        (by
          have h : ((childLL thetaBelowCell1111331131011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011323) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011323) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011323) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011323) h))

theorem cover_subtree_8b305093aef1 :
    adaptiveCoverCheck 3 (childHH (childHH (childLH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
    thetaBelowCell111133113101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011330
        (by
          have h : ((childLL thetaBelowCell1111331131011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011330) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011330) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011330) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011331
        (by
          have h : ((childLL thetaBelowCell1111331131011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011331) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011331) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011331) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011331) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011332
        (by
          have h : ((childLL thetaBelowCell1111331131011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011332) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011332) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011332) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011333
        (by
          have h : ((childLL thetaBelowCell1111331131011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011333) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011333) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011333) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011333) h))

theorem cover_subtree_38619e7e6aac :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113101))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131011300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011300 h)
        (by
          have h : (thetaBelowCell1111331131011301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011301 h)
        (by
          have h : (thetaBelowCell1111331131011302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011302 h)
        (by
          have h : (thetaBelowCell1111331131011303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131011310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011310 h)
        (by
          have h : (thetaBelowCell1111331131011311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011311 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011312
            (by
              have h : ((childLL thetaBelowCell1111331131011312)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011312)
                h)
            (by
              have h : ((childLH thetaBelowCell1111331131011312)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011312)
                h)
            (by
              have h : ((childHL thetaBelowCell1111331131011312)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011312)
                h)
            (by
              have h : ((childHH thetaBelowCell1111331131011312)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011312)
                h))
        (by
          have h : (thetaBelowCell1111331131011313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011313 h))
    cover_subtree_4f3cdd0c257d
    cover_subtree_8b305093aef1

theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c1 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113101)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113101))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133113101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133113101))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133113101))) h))
    cover_subtree_cac2e3b1401d
    cover_subtree_38619e7e6aac

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3846b81fdf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))
/-- Subcell `0000220021003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022002100)))

end CertificateCells3846b81fdf

open CertificateCells3846b81fdf
theorem cover_subtree_c9cdbb673d76 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003002 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003002
    (by
      have h : ((childLL thetaAboveCell0000220021003002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003002) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003002) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003002)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003002)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003002)) h))

theorem cover_subtree_0d25773c4d7a :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003003 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003003
    (by
      have h : ((childLL thetaAboveCell0000220021003003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003003) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003003) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003003)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003003)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003003)) h))

theorem cover_subtree_d91230c1595a :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021003000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003000 h)
    (by
      have h : (thetaAboveCell0000220021003001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003001 h)
    cover_subtree_c9cdbb673d76
    cover_subtree_0d25773c4d7a

theorem cover_subtree_3b00f6acc230 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003012 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003012
    (by
      have h : ((childLL thetaAboveCell0000220021003012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003012) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003012) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003012)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003012)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003012)) h))

theorem cover_subtree_7ad163274380 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003013 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003013
    (by
      have h : ((childLL thetaAboveCell0000220021003013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003013) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003013) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003013)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003013)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003013)) h))

theorem cover_subtree_5685dda3095f :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021003010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003010 h)
    (by
      have h : (thetaAboveCell0000220021003011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003011 h)
    cover_subtree_3b00f6acc230
    cover_subtree_7ad163274380

theorem cover_subtree_f7f8133fac9a :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003020 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003020
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003020)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003020)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003020)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003020)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003020)) h))

theorem cover_subtree_34eb89665f6e :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003021 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003021
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003021)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003021)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003021)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003021)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003021)) h))

theorem cover_subtree_854759339591 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022002100)))
    cover_subtree_f7f8133fac9a
    cover_subtree_34eb89665f6e
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003022
        (by
          have h : ((childLL thetaAboveCell0000220021003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003023
        (by
          have h : ((childLL thetaAboveCell0000220021003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003023) h))

theorem cover_subtree_a49deaaa8f12 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003030 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003030
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003030)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003030)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003030)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003030)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003030)) h))

theorem cover_subtree_2236023309b5 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003031 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003031
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003031)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003031)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003031)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003031)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003031)) h))

theorem cover_subtree_2c168101607b :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022002100)))
    cover_subtree_a49deaaa8f12
    cover_subtree_2236023309b5
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003032
        (by
          have h : ((childLL thetaAboveCell0000220021003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003033
        (by
          have h : ((childLL thetaAboveCell0000220021003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003033) h))

theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c0 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002100))
    cover_subtree_d91230c1595a
    cover_subtree_5685dda3095f
    cover_subtree_854759339591
    cover_subtree_2c168101607b

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8d8f6e86b1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002200)))

end CertificateCells8d8f6e86b1

open CertificateCells8d8f6e86b1
theorem e24KC2ThetaAboveLeaf0000220021_c1_c2 :
    adaptiveCoverCheck 7 thetaAboveCell000022002112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002112)
        (by
          have h : ((childLL (childLL thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022002112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002112)
        (by
          have h : ((childLL (childLH thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022002112)) h))
    (by
      have h : ((childHL thetaAboveCell000022002112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022002112) h)
    (by
      have h : ((childHH thetaAboveCell000022002112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022002112) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells67d4ab08b2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))
/-- Subcell `0000220021003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022002100)))
/-- Subcell `0000220021003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022002100)))

end CertificateCells67d4ab08b2

open CertificateCells67d4ab08b2
theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022002100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003200 h)
        (by
          have h : (thetaAboveCell0000220021003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003201 h)
        (by
          have h : (thetaAboveCell0000220021003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003202 h)
        (by
          have h : (thetaAboveCell0000220021003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003210 h)
        (by
          have h : (thetaAboveCell0000220021003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003211 h)
        (by
          have h : (thetaAboveCell0000220021003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003212 h)
        (by
          have h : (thetaAboveCell0000220021003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022002100))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022002100))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells37e4000123

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133113113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell11113311)))

end CertificateCells37e4000123

open CertificateCells37e4000123
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c3 :
    adaptiveCoverCheck 6 thetaBelowCell111133113113 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113113
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113113)
        (by
          have h : ((childLL (childLL thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113113)
        (by
          have h : ((childLL (childLH thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133113113)) h))
    (by
      have h : ((childHL thetaBelowCell111133113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113113) h)
    (by
      have h : ((childHH thetaBelowCell111133113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113113) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells61d6915992

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end CertificateCells61d6915992

open CertificateCells61d6915992
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c2 :
    adaptiveCoverCheck 4 (childHL (childHH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHL (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHL (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHL (childHL (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHH (childHL (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
        thetaBelowCell111133113111))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells49a6e2db55

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end CertificateCells49a6e2db55

open CertificateCells49a6e2db55
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c3 :
    adaptiveCoverCheck 4 (childHH (childHL thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHH (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHH (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHL (childHH (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHH (childHH (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
        thetaBelowCell111133113111))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells23cc985c42

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end CertificateCells23cc985c42

open CertificateCells23cc985c42

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133113111) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113111)
    e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c0 e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c1
      e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c2 e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c3

end PartE
end GerverSofa

end

end

end
