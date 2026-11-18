/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4418T3EndpointOwnerIndices
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms

-- [TABLET NODE: P5485T1OtherCompanionCoordinates]

/-!
# P5485T1OtherCompanionCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5485T1OtherCompanionCoordinates
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b)
    (i j k s : Fin 3) (positive sign : Bool)
    (hcyclic : (i = 0 ∧ j = 1 ∧ k = 2) ∨
      (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 0 ∧ k = 1))
    (hselected : (s = i ∧ sign = positive) ∨
      (s = j ∧ sign = !positive))
    (hindex : a =
      let label : SixSubtileLabel := match s.val with
        | 0 => if sign then .A else .B
        | 1 => if sign then .C else .D
        | _ => if sign then .E else .F
      let coord : Int × Int := match k.val with
        | 0 => (1, 0) | 1 => (0, 1) | _ => (-1, -1)
      let scale : Int := if positive then 1 else -1
      ⟨label, scale * coord.1, scale * coord.2⟩) :
    let other := if s = i then j else i
    let coord : Int × Int := match other.val with
      | 0 => (1, 0) | 1 => (0, 1) | _ => (-1, -1)
    let scale : Int := if positive then -1 else 1
    let m := scale * coord.1
    let n := scale * coord.2
    (if positive then (-1 : GaussianInt) else 1) *
        BandVectors.1 (q 0) (q other.succ) =
      (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v ∧
    (a.first, a.second) ≠ (m, n) ∧
    (b.first, b.second) ≠ (m, n) ∧
    ((P4418T3EndpointOwnerIndices q cfg C T cert a b row).1.first,
      (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1.second) ≠ (m, n) ∧
    ((P4418T3EndpointOwnerIndices q cfg C T cert a b row).2.first,
      (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2.second) ≠ (m, n) := by
-- BODY
  have hu : BandVectors.1 (q 0) (q 1) = cert.u := cert.period_u.symm
  have hv : BandVectors.1 (q 0) (q 2) = cert.v := cert.period_v.symm
  have hw : BandVectors.1 (q 0) (q 3) = -cert.u - cert.v := by
    obtain ⟨_, _, _, _, h1, h2, h3, _⟩ := P3055T1ParentVectorNormalForms q cfg
    rw [← hu, ← hv, h1, h2, h3]
    ring
  rcases hcyclic with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals cases positive
  all_goals rcases hselected with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals cases row
  all_goals simp_all [P4418T3EndpointOwnerIndices, Fin.succ]
  all_goals ring

end ApollonianSuperharmonic

end
