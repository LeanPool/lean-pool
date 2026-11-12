/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.RightSubtileOdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.PartialOdometerHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P5589T1EndpointCompatibility]

/-!
# P5589T1EndpointCompatibility

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5589T1EndpointCompatibility
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (C D : BandCircle) (i : Fin 3) (hC : q 0 = C.1.1) (hD : q i.succ = D.1.1)
    (U R S : ProtoTile) (f k hm hp : PartialOdometer)
    (hOf : TileOdometer C.1.1 U f)
    (hOm : TileOdometer D.1.1 R hm) (hOp : TileOdometer D.1.1 S hp)
    (p pm pp : ℝ × ℝ)
    (hsf : PartialOdometerSlope f = some p)
    (hsm : PartialOdometerSlope hm = some pm)
    (hsp : PartialOdometerSlope hp = some pp)
    (hcm : TileCentroid R - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.1 (q i.succ) (q 0) - BandVectors.1 (q 0) (q i.succ)))
    (hcp : TileCentroid S - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ)))
    (hpm : pm - p = (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ)))
    (hpp : pp - p = (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)))
    (d a : GaussianInt) (b bm bp : ℤ)
    (hk : k = PartialOdometerAffineTranslate (PartialOdometerHalfTurn f) d a b)
    (hhp : hp = PartialOdometerAffineTranslate (PartialOdometerHalfTurn hm) d a bm)
    (hhm : hm = PartialOdometerAffineTranslate (PartialOdometerHalfTurn hp) d a bp) :
    OdometerCompatibility f hm ∧ OdometerCompatibility f hp ∧
      OdometerCompatibility k hm ∧ OdometerCompatibility k hp := by
-- BODY
  have flips := (VectorRecursionLaws q hq.1).2.2.2.2 hq i
  have cm : TileCentroid R - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint
      ((⟨0,1⟩ : GaussianInt) ^ (3 : Fin 4).val *
        (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) := by
    rw [hcm, flips.1]
    congr 2
    ext <;> simp [pow_succ] <;> ring
  have sm : pm - p = (1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0,1⟩ : GaussianInt) ^ (3 : Fin 4).val *
        (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))) := by
    rw [hpm, flips.2]
    congr 2
    ext <;> simp [pow_succ]; ring
  have hfm : OdometerCompatibility f hm :=
    RightSubtileOdometerCompatibility.2 C D U R f hm
      ⟨hOf, hOm, p, pm, hsf, hsm, q, i, 3, hq, hC, hD, cm,
        congrArg Prod.fst sm, congrArg Prod.snd sm⟩
  have hfp : OdometerCompatibility f hp :=
    RightSubtileOdometerCompatibility.2 C D U S f hp
      ⟨hOf, hOp, p, pp, hsf, hsp, q, i, 0, hq, hC, hD,
        by simpa using hcp, by simpa using congrArg Prod.fst hpp,
        by simpa using congrArg Prod.snd hpp⟩
  have reflect (v w : PartialOdometer) (c e : ℤ)
      (h : OdometerCompatibility v w) :
      OdometerCompatibility
        (PartialOdometerAffineTranslate (PartialOdometerHalfTurn v) d a c)
        (PartialOdometerAffineTranslate (PartialOdometerHalfTurn w) d a e) := by
    have mem (v : PartialOdometer) (c : ℤ) (x : GaussianInt) :
        x ∈ (PartialOdometerAffineTranslate (PartialOdometerHalfTurn v) d a c).domain ↔
          -(x-d) ∈ v.domain := by
      rw [(PartialOdometerAffineTranslateFormulas _ _ _ _).2.1,
        (PartialOdometerHalfTurnFormulas _).1]
    rcases h with hd | ⟨t, ht⟩
    · left
      exact Set.disjoint_left.mpr (fun x hx hy =>
        Set.disjoint_left.mp hd ((mem v c x).mp hx) ((mem w e x).mp hy))
    · right
      refine ⟨t+e-c, ?_⟩
      intro x hx hy
      have he := ht (-(x-d)) ((mem v c x).mp hx) ((mem w e x).mp hy)
      rw [(PartialOdometerAffineTranslateFormulas _ _ _ _).2.2.1 x hy,
        (PartialOdometerAffineTranslateFormulas _ _ _ _).2.2.1 x hx,
        (PartialOdometerHalfTurnFormulas w).2.1 (x-d)
          ((PartialOdometerAffineTranslateFormulas _ _ _ _).2.1 x |>.mp hy),
        (PartialOdometerHalfTurnFormulas v).2.1 (x-d)
          ((PartialOdometerAffineTranslateFormulas _ _ _ _).2.1 x |>.mp hx)]
      omega
  refine ⟨hfm, hfp, ?_, ?_⟩
  · rw [hk, hhm]
    exact reflect f hp b bp hfp
  · rw [hk, hhp]
    exact reflect f hm b bm hfm

end ApollonianSuperharmonic

end
