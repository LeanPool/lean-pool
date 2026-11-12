/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.CurvatureOneOdometer
public import LeanPool.ApollonianSuperharmonic.OdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.OdometerTranslation
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: TileOdometerAffineTranslation]

/-!
# TileOdometerAffineTranslation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileOdometerAffineTranslation
    (C : CircleCoordinates) (T : ProtoTile) (h : PartialOdometer)
    (u a : GaussianInt) (b : ℤ) (hO : TileOdometer C T h) :
    TileOdometer C (TileTranslation T u)
      (PartialOdometerAffineTranslate h u a b) := by
-- BODY
  induction hO with
  | line w x hw h hdom =>
      change TileOdometer (0, w) ⟨∅, GaussianTranslation u x⟩
        (PartialOdometerAffineTranslate h u a b)
      refine TileOdometer.line w (GaussianTranslation u x) hw
        (PartialOdometerAffineTranslate h u a b) ?_
      rw [PartialOdometerAffineTranslateFormulas h u a b |>.1, hdom]
      simp [GaussianTranslation]
  | unit z x T h hT hdom htrans =>
      refine TileOdometer.unit z (GaussianTranslation u x)
        (TileTranslation T u)
        (PartialOdometerAffineTranslate h u a b) ?_ ?_ ?_
      · rw [(TileTranslationFormulas T u).1, hT]
        simp [GaussianTranslation]
      · exact ((PartialOdometerAffineTranslateFormulas h u a b).2.2.2.2.1)
          _ hdom
      · rcases htrans with ⟨v, c, d, hv, hval⟩
        refine ⟨GaussianTranslation u v, c + a,
          d - c.re * u.re - c.im * u.im + b, ?_, ?_⟩
        · intro y
          constructor
          · intro hy
            have hy' := ((PartialOdometerAffineTranslateFormulas h u a b).2.1 y).mp hy
            simpa [GaussianTranslation, sub_eq_add_neg, add_assoc, add_comm,
              add_left_comm] using (hv (y - u)).mp hy'
          · intro hy
            apply ((PartialOdometerAffineTranslateFormulas h u a b).2.1 y).mpr
            apply (hv (y - u)).mpr
            simpa [GaussianTranslation, sub_eq_add_neg, add_assoc, add_comm,
              add_left_comm] using hy
        · intro y hy
          rw [(PartialOdometerAffineTranslateFormulas h u a b).2.2.1 y hy]
          rw [hval (y - u) (((PartialOdometerAffineTranslateFormulas h u a b).2.1 y).mp hy)]
          dsimp [GaussianTranslation]
          ring_nf
  | @decompose qd hq Sd Td hsd hd hT hsub hcells hfoot hcentroid hdom hvalue hcompat hslope ih =>
      refine TileOdometer.decompose (q := qd)
        (S := fun i s => TileTranslation (Sd i s) u)
        (T := TileTranslation Td u)
        (hs := fun i s => PartialOdometerAffineTranslate (hsd i s) u a b)
        (h := PartialOdometerAffineTranslate hd u a b) hq
        (BandPrototileTranslation _ Td u hT) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro i s
        exact ih i s
      · intro x
        rw [(TileTranslationFormulas Td u).1]
        change x ∈ Td.cells.image (GaussianTranslation u) ↔
          ∃ i s, x ∈ (Sd i s).cells.image (GaussianTranslation u)
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨i, s, hy'⟩ := (hcells y).mp hy
          exact ⟨i, s, y, hy', rfl⟩
        · rintro ⟨i, s, y, hy, rfl⟩
          exact ⟨y, (hcells y).mpr ⟨i, s, hy⟩, rfl⟩
      · intro i s x hx
        obtain ⟨y, hy, rfl⟩ := by
          simpa only [(TileTranslationFormulas (Sd i s) u).2.2.2.2.2.1]
            using hx
        have hy' := hfoot i s hy
        rw [(TileTranslationFormulas Td u).2.2.2.2.2.1]
        exact ⟨y, hy', rfl⟩
      · intro i s
        obtain ⟨_, _, _, _, fS, _, _⟩ := TileTranslationFormulas (Sd i s) u
        obtain ⟨_, _, _, _, fT, _, _⟩ := TileTranslationFormulas Td u
        rw [fS, fT]
        dsimp
        convert hcentroid i s using 1; ext <;>
          simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      · intro x
        constructor
        · intro hx
          obtain ⟨i, s, hy⟩ := (hdom (x - u)).mp
            (((PartialOdometerAffineTranslateFormulas hd u a b).2.1 x).mp hx)
          exact ⟨i, s, ((PartialOdometerAffineTranslateFormulas (hsd i s) u a b).2.1 x).mpr hy⟩
        · rintro ⟨i, s, hx⟩
          apply ((PartialOdometerAffineTranslateFormulas hd u a b).2.1 x).mpr
          apply (hdom (x - u)).mpr
          exact ⟨i, s, ((PartialOdometerAffineTranslateFormulas (hsd i s) u a b).2.1 x).mp hx⟩
      · intro i s x hx
        have hx' := ((PartialOdometerAffineTranslateFormulas (hsd i s) u a b).2.1 x).mp hx
        have hxo := (hdom (x - u)).mpr ⟨i, s, hx'⟩
        have hxo' := ((PartialOdometerAffineTranslateFormulas hd u a b).2.1 x).mpr hxo
        rw [(PartialOdometerAffineTranslateFormulas hd u a b).2.2.1 x hxo']
        rw [(PartialOdometerAffineTranslateFormulas (hsd i s) u a b).2.2.1 x hx]
        rw [hvalue i s (x - u) hx']
      · intro i s j t
        rcases hcompat i s j t with hd | ⟨c, hc⟩
        · left
          apply Set.disjoint_left.2
          intro x hx hy
          apply Set.disjoint_left.1 hd
          · exact ((PartialOdometerAffineTranslateFormulas (hsd i s) u a b).2.1 x).mp hx
          · exact ((PartialOdometerAffineTranslateFormulas (hsd j t) u a b).2.1 x).mp hy
        · right
          refine ⟨c, ?_⟩
          intro x hx hy
          have hxi := ((PartialOdometerAffineTranslateFormulas (hsd i s) u a b).2.1 x).mp hx
          have hxj := ((PartialOdometerAffineTranslateFormulas (hsd j t) u a b).2.1 x).mp hy
          rw [(PartialOdometerAffineTranslateFormulas (hsd j t) u a b).2.2.1 x hy]
          rw [(PartialOdometerAffineTranslateFormulas (hsd i s) u a b).2.2.1 x hx]
          have hc' := hc (x - u) hxi hxj
          linarith
      · intro i s
        rcases hslope i s with hz | ⟨p, pi, hp, hpi, hdx, hdy⟩
        · exact Or.inl hz
        · right
          refine ⟨(p.1 + (a.re : ℝ), p.2 + (a.im : ℝ)),
            (pi.1 + (a.re : ℝ), pi.2 + (a.im : ℝ)), ?_, ?_, ?_, ?_⟩
          · simpa [PartialOdometerAffineTranslateFormulas hd u a b] using hp
          · simpa [PartialOdometerAffineTranslateFormulas (hsd i s) u a b] using hpi
          · dsimp
            linarith
          · dsimp
            linarith

end ApollonianSuperharmonic

end
