/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricOccurrence
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: QuarterTurnSymmetricCenteredTransport]

/-!
# QuarterTurnSymmetricCenteredTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CenteredTransportLemmas

private theorem center_mem :
    ∀ (S : ProtoTile), ∀ (x : GaussianInt), x ∈ S.cells ↔
        (((x.re : Int) : Real) + (1 / 2 : Real),
          ((x.im : Int) : Real) + (1 / 2 : Real)) ∈ TileRealization S := by
  classical
  intro S x
  constructor
  · intro hx
    change (((x.re : Int) : Real) + (1 / 2 : Real),
      ((x.im : Int) : Real) + (1 / 2 : Real)) ∈
        ⋃ y ∈ S.cells, ClosedSquareRealization y
    simp only [Set.mem_iUnion]
    refine ⟨x, hx, ?_⟩
    simp [ClosedSquareRealization]
    norm_num
  · intro hp
    change (((x.re : Int) : Real) + (1 / 2 : Real),
      ((x.im : Int) : Real) + (1 / 2 : Real)) ∈
        ⋃ y ∈ S.cells, ClosedSquareRealization y at hp
    simp only [Set.mem_iUnion] at hp
    rcases hp with ⟨y, hy, hbox⟩
    simp only [ClosedSquareRealization, Set.mem_Icc] at hbox
    have re_one : (y.re : Int) < x.re + 1 := by
      exact_mod_cast (show (y.re : Real) < (x.re : Real) + 1 by linarith [hbox.1.1])
    have re_two : x.re < (y.re : Int) + 1 := by
      exact_mod_cast (show (x.re : Real) < (y.re : Real) + 1 by linarith [hbox.2.1])
    have im_one : (y.im : Int) < x.im + 1 := by
      exact_mod_cast (show (y.im : Real) < (x.im : Real) + 1 by linarith [hbox.1.2])
    have im_two : x.im < (y.im : Int) + 1 := by
      exact_mod_cast (show (x.im : Real) < (y.im : Real) + 1 by linarith [hbox.2.2])
    have re_eq : y.re = x.re := by omega
    have im_eq : y.im = x.im := by omega
    have xy : y = x := by
      cases y
      cases x
      rw [Zsqrtd.ext_iff]
      exact ⟨re_eq, im_eq⟩
    simpa [xy] using hy

end CenteredTransportLemmas

theorem QuarterTurnSymmetricCenteredTransport : ∀ (T : ProtoTile),
    QuarterTurnSymmetric T →
    ∃ u : GaussianInt,
      GaussianRealPoint u =
        ((TileCentroid T).1 + (TileCentroid T).2,
          (TileCentroid T).2 - (TileCentroid T).1) ∧
      (TileTranslation (TileQuarterTurn T) u).cells = T.cells ∧
      ((T.cells = ∅) →
        (TileTranslation (TileQuarterTurn T) u).anchor = T.anchor) ∧
      FootprintVertices (TileTranslation (TileQuarterTurn T) u) =
        FootprintVertices T ∧
      TileCentroid (TileTranslation (TileQuarterTurn T) u) =
        TileCentroid T := by
-- BODY
  intro T hT
  have center_mem : ∀ (S : ProtoTile) (x : GaussianInt),
      x ∈ S.cells ↔
        (((x.re : Int) : Real) + (1 / 2 : Real),
          ((x.im : Int) : Real) + (1 / 2 : Real)) ∈ TileRealization S :=
              CenteredTransportLemmas.center_mem
  by_cases hempty : T.cells = ∅
  · let u : GaussianInt :=
      ⟨T.anchor.re + T.anchor.im, T.anchor.im - T.anchor.re⟩
    have hc : TileCentroid T =
        ((((T.anchor.re : Int) : Real)), (((T.anchor.im : Int) : Real))) := by
      change (if T.cells.Nonempty then _ else
        ((((T.anchor.re : Int) : Real)), (((T.anchor.im : Int) : Real)))) = _
      rw [ite_eq_right]
      exact Finset.not_nonempty_iff_eq_empty.mpr hempty
    have hu : GaussianRealPoint u =
        ((TileCentroid T).1 + (TileCentroid T).2,
          (TileCentroid T).2 - (TileCentroid T).1) := by
      rw [hc]
      dsimp [u, GaussianRealPoint]
      norm_num
    have ho := QuarterTurnSymmetricOccurrence T u hT hu
    have qt := TileQuarterTurnFormulas T
    have tr := TileTranslationFormulas (TileQuarterTurn T) u
    have hf : FootprintVertices (TileTranslation (TileQuarterTurn T) u) =
        FootprintVertices T := by
      simp only [FootprintVertices]
      rw [ho.1, ho.2 hempty]
    have hcent : TileCentroid (TileTranslation (TileQuarterTurn T) u) =
        TileCentroid T := by
      rw [tr.2.2.2.2.1, qt.2.2.2.2.1, hc]
      dsimp [u]
      norm_num
    exact ⟨u, hu, ho.1, fun _ => ho.2 hempty, hf, hcent⟩
  · have hne : T.cells.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let real_parts := T.cells.image (fun x => x.re)
    let imag_parts := T.cells.image (fun x => x.im)
    have real_ne : real_parts.Nonempty := hne.image _
    have imag_ne : imag_parts.Nonempty := hne.image _
    let xmin : Int := real_parts.min' real_ne
    let xmax : Int := real_parts.max' real_ne
    let ymin : Int := imag_parts.min' imag_ne
    let ymax : Int := imag_parts.max' imag_ne
    have lower_re : ∀ p : Real × Real, p ∈ TileRealization T →
        (xmin : Real) ≤ p.1 := by
      intro p hp
      change p ∈ ⋃ y ∈ T.cells, ClosedSquareRealization y at hp
      simp only [Set.mem_iUnion] at hp
      rcases hp with ⟨y, hy, hb⟩
      simp only [ClosedSquareRealization, Set.mem_Icc] at hb
      have hm : xmin ≤ y.re := by
        exact Finset.min'_le real_parts y.re (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      exact le_trans (by simpa only [Prod.fst] using (show (xmin : Real) ≤ (y.re : Real) by
          exact_mod_cast hm)) hb.1.1
    have upper_im : ∀ p : Real × Real, p ∈ TileRealization T →
        p.2 ≤ (ymax : Real) + 1 := by
      intro p hp
      change p ∈ ⋃ y ∈ T.cells, ClosedSquareRealization y at hp
      simp only [Set.mem_iUnion] at hp
      rcases hp with ⟨y, hy, hb⟩
      simp only [ClosedSquareRealization, Set.mem_Icc] at hb
      have hm : y.im ≤ ymax := by
        exact Finset.le_max' imag_parts y.im (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      have hh : (y.im : Real) ≤ (ymax : Real) := by exact_mod_cast hm
      exact le_trans hb.2.2 (by linarith)
    have lower_im : ∀ p : Real × Real, p ∈ TileRealization T →
        (ymin : Real) ≤ p.2 := by
      intro p hp
      change p ∈ ⋃ y ∈ T.cells, ClosedSquareRealization y at hp
      simp only [Set.mem_iUnion] at hp
      rcases hp with ⟨y, hy, hb⟩
      simp only [ClosedSquareRealization, Set.mem_Icc] at hb
      have hm : ymin ≤ y.im := by
        exact Finset.min'_le imag_parts y.im (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      exact le_trans (by simpa only [Prod.snd] using (show (ymin : Real) ≤ (y.im : Real) by
          exact_mod_cast hm)) hb.1.2
    have lower_pt : ∃ p : Real × Real, p ∈ TileRealization T ∧ p.1 = (xmin : Real) := by
      obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp (Finset.min'_mem real_parts real_ne)
      have hxmin : xmin = x.re := by exact hxr.symm
      refine ⟨((xmin : Real), (x.im : Real)), ?_, ?_⟩
      · change _ ∈ ⋃ y ∈ T.cells, ClosedSquareRealization y
        simp only [Set.mem_iUnion]
        refine ⟨x, hx, ?_⟩
        simp [ClosedSquareRealization, hxmin]
      · rfl
    have lower_pt_im : ∃ p : Real × Real, p ∈ TileRealization T ∧ p.2 = (ymin : Real) := by
      obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp (Finset.min'_mem imag_parts imag_ne)
      have hymin : ymin = x.im := by exact hxr.symm
      refine ⟨((x.re : Real), (ymin : Real)), ?_, ?_⟩
      · change _ ∈ ⋃ y ∈ T.cells, ClosedSquareRealization y
        simp only [Set.mem_iUnion]
        refine ⟨x, hx, ?_⟩
        simp [ClosedSquareRealization, hymin]
      · rfl
    have upper_pt : ∃ p : Real × Real, p ∈ TileRealization T ∧ p.2 = (ymax : Real) + 1 := by
      obtain ⟨y, hy, hyr⟩ := Finset.mem_image.mp (Finset.max'_mem imag_parts imag_ne)
      have hymax : ymax = y.im := by exact hyr.symm
      refine ⟨((y.re : Real), (ymax : Real) + 1), ?_, ?_⟩
      · change _ ∈ ⋃ z ∈ T.cells, ClosedSquareRealization z
        simp only [Set.mem_iUnion]
        refine ⟨y, hy, ?_⟩
        simp [ClosedSquareRealization, hymax]
      · rfl
    let c := TileCentroid T
    have image_mem (p : Real × Real) (hp : p ∈ TileRealization T) :
        (c.1 - (p.2 - c.2), c.2 + (p.1 - c.1)) ∈ TileRealization T :=
      (hT p).mp hp
    have image_twice (p : Real × Real) (hp : p ∈ TileRealization T) :
        (c.1 - ((c.2 + (p.1 - c.1)) - c.2),
          c.2 + ((c.1 - (p.2 - c.2)) - c.1)) ∈ TileRealization T := by
      exact image_mem _ (image_mem p hp)
    have image_thrice (p : Real × Real) (hp : p ∈ TileRealization T) :
        (c.1 - ((c.2 + ((c.1 - (p.2 - c.2)) - c.1)) - c.2),
          c.2 + ((c.1 - ((c.2 + (p.1 - c.1)) - c.2)) - c.1)) ∈ TileRealization T := by
      exact image_mem _ (image_twice p hp)
    have image_lower (p : Real × Real) (hp : p ∈ TileRealization T) :
        (xmin : Real) ≤ c.1 - (p.2 - c.2) :=
      lower_re _ (image_mem p hp)
    have image_lower_second (p : Real × Real) (hp : p ∈ TileRealization T) :
        (ymin : Real) ≤ c.2 + (p.1 - c.1) :=
      lower_im _ (image_mem p hp)
    have first_eq : c.1 + c.2 = (xmin : Real) + (ymax : Real) + 1 := by
      obtain ⟨p, hp, hpy⟩ := upper_pt
      have h₁ := image_lower p hp
      obtain ⟨q, hq, hqx⟩ := lower_pt
      let r := (c.1 - ((c.2 + ((c.1 - (q.2 - c.2)) - c.1)) - c.2),
          c.2 + ((c.1 - ((c.2 + (q.1 - c.1)) - c.2)) - c.1))
      have hr : r ∈ TileRealization T := by
        exact image_thrice q hq
      have h₂ := upper_im r hr
      have hre : q.1 = c.1 + c.2 - r.2 := by
        dsimp [r]
        ring
      change r.2 ≤ (ymax : Real) + 1 at h₂
      rw [hpy] at h₁
      rw [hqx] at hre
      linarith
    have second_eq : c.2 - c.1 = (ymin : Real) - (xmin : Real) := by
      obtain ⟨p, hp, hpx⟩ := lower_pt
      have h₁ := image_lower_second p hp
      obtain ⟨q, hq, hqy⟩ := lower_pt_im
      let r := (c.1 - ((c.2 + ((c.1 - (q.2 - c.2)) - c.1)) - c.2),
          c.2 + ((c.1 - ((c.2 + (q.1 - c.1)) - c.2)) - c.1))
      have hr : r ∈ TileRealization T := by
        exact image_thrice q hq
      have h₂ := lower_re r hr
      change (xmin : Real) ≤ r.1 at h₂
      rw [hpx] at h₁
      have hre : q.2 = c.2 - c.1 + r.1 := by
        dsimp [r]
        ring
      rw [hqy] at hre
      linarith
    let u : GaussianInt := ⟨xmin + ymax + 1, ymin - xmin⟩
    have hu : GaussianRealPoint u =
        ((TileCentroid T).1 + (TileCentroid T).2,
          (TileCentroid T).2 - (TileCentroid T).1) := by
      dsimp [u, GaussianRealPoint]
      exact Prod.ext (by exact_mod_cast first_eq.symm) (by exact_mod_cast second_eq.symm)
    have ho := QuarterTurnSymmetricOccurrence T u hT hu
    have qt := TileQuarterTurnFormulas T
    have tr := TileTranslationFormulas (TileQuarterTurn T) u
    have hf : FootprintVertices (TileTranslation (TileQuarterTurn T) u) =
        FootprintVertices T := by
      simp only [FootprintVertices]
      have hnew : (TileTranslation (TileQuarterTurn T) u).cells.Nonempty := by
        rw [ho.1]
        exact hne
      rw [ite_eq_left hnew, ite_eq_left hne, ho.1]
    have hcent : TileCentroid (TileTranslation (TileQuarterTurn T) u) =
        TileCentroid T := by
      rw [tr.2.2.2.2.1, qt.2.2.2.2.1]
      dsimp [u]
      have a := congrArg Prod.fst hu
      have b := congrArg Prod.snd hu
      dsimp [GaussianRealPoint] at a b
      rw [Prod.ext_iff]
      constructor <;> linarith
    exact ⟨u, hu, ho.1, fun h => (hempty h).elim, hf, hcent⟩

end ApollonianSuperharmonic

end
