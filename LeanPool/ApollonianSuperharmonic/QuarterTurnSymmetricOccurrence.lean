/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: QuarterTurnSymmetricOccurrence]

/-!
# QuarterTurnSymmetricOccurrence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem QuarterTurnSymmetricOccurrence :
    ∀ (T : ProtoTile) (u : GaussianInt),
    QuarterTurnSymmetric T →
    GaussianRealPoint u =
      ((TileCentroid T).1 + (TileCentroid T).2,
        (TileCentroid T).2 - (TileCentroid T).1) →
    (TileTranslation (TileQuarterTurn T) u).cells = T.cells ∧
      (T.cells = ∅ →
        (TileTranslation (TileQuarterTurn T) u).anchor = T.anchor) := by
-- BODY
  intro T u hT hu
  have quarter := TileQuarterTurnFormulas T
  have translate := TileTranslationFormulas (TileQuarterTurn T) u
  have coordinate_re : (u.re : Real) = (TileCentroid T).1 + (TileCentroid T).2 := by
    have h := congrArg Prod.fst hu
    simpa [GaussianRealPoint] using h
  have coordinate_im : (u.im : Real) = (TileCentroid T).2 - (TileCentroid T).1 := by
    have h := congrArg Prod.snd hu
    simpa [GaussianRealPoint] using h
  have realization_same :
      TileRealization (TileTranslation (TileQuarterTurn T) u) =
        TileRealization T := by
    let rotate : (Real × Real) → (Real × Real) := fun p =>
      ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
        (TileCentroid T).2 + (p.1 - (TileCentroid T).1))
    have rotate_mem : ∀ p : Real × Real,
        p ∈ TileRealization T ↔ rotate p ∈ TileRealization T := by
      intro p
      exact hT p
    have rotate_four : ∀ p : Real × Real, rotate (rotate (rotate (rotate p))) = p := by
      intro p
      dsimp [rotate]
      congr 1 <;> ring
    rw [translate.2.2.2.1, quarter.2.2.2.1]
    have map_formula : ∀ p : Real × Real,
        (fun q : Real × Real => (q.1 + (u.re : Real), q.2 + (u.im : Real)))
            (-p.2, p.1) = rotate p := by
      intro p
      dsimp [rotate]
      rw [coordinate_re, coordinate_im]
      congr 1 <;> ring
    have image_formula :
        (fun q : Real × Real => (q.1 + (u.re : Real), q.2 + (u.im : Real))) ''
            ((fun p : Real × Real => (-p.2, p.1)) '' TileRealization T) =
          rotate '' TileRealization T := by
      ext p
      simp only [Set.mem_image]
      constructor
      · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
        exact ⟨r, hr, (map_formula r).symm⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨(-r.2, r.1), ⟨r, hr, rfl⟩, map_formula r⟩
    rw [image_formula]
    ext p
    simp only [Set.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (rotate_mem q).mp hq
    · intro hp
      refine ⟨rotate (rotate (rotate p)), ?_, ?_⟩
      · exact (rotate_mem (rotate (rotate p))).mp
          ((rotate_mem (rotate p)).mp ((rotate_mem p).mp hp))
      · rw [rotate_four]
  have center_mem : ∀ (S : ProtoTile) (x : GaussianInt),
      x ∈ S.cells ↔
        (((x.re : Int) : Real) + (1 / 2 : Real),
          ((x.im : Int) : Real) + (1 / 2 : Real)) ∈ TileRealization S := by
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
      have re_lower : (y.re : Real) ≤ (x.re : Real) + (1 / 2 : Real) := hbox.1.1
      have re_upper : (x.re : Real) + (1 / 2 : Real) ≤ (y.re : Real) + 1 := hbox.2.1
      have im_lower : (y.im : Real) ≤ (x.im : Real) + (1 / 2 : Real) := hbox.1.2
      have im_upper : (x.im : Real) + (1 / 2 : Real) ≤ (y.im : Real) + 1 := hbox.2.2
      have re_one : (y.re : Int) < x.re + 1 := by
        exact_mod_cast (show (y.re : Real) < (x.re : Real) + 1 by linarith)
      have re_two : x.re < (y.re : Int) + 1 := by
        exact_mod_cast (show (x.re : Real) < (y.re : Real) + 1 by linarith)
      have im_one : (y.im : Int) < x.im + 1 := by
        exact_mod_cast (show (y.im : Real) < (x.im : Real) + 1 by linarith)
      have im_two : x.im < (y.im : Int) + 1 := by
        exact_mod_cast (show (x.im : Real) < (y.im : Real) + 1 by linarith)
      have re_eq : y.re = x.re := by omega
      have im_eq : y.im = x.im := by omega
      have xy : y = x := by
        cases y
        cases x
        rw [Zsqrtd.ext_iff]
        exact ⟨re_eq, im_eq⟩
      simpa [xy] using hy
  constructor
  · have cell_formula := translate.1
    rw [cell_formula, quarter.1]
    apply Finset.ext
    intro x
    constructor
    · intro hx
      change x ∈ (TileTranslation (TileQuarterTurn T) u).cells at hx
      have hxcenter := (center_mem (TileTranslation (TileQuarterTurn T) u) x).mp hx
      have hnew :
          (((x.re : Int) : Real) + (1 / 2 : Real),
            ((x.im : Int) : Real) + (1 / 2 : Real)) ∈ TileRealization T := by
        rw [← realization_same]
        exact hxcenter
      exact (center_mem T x).mpr hnew
    · intro hx
      have hxcenter := (center_mem T x).mp hx
      have hnew :
          (((x.re : Int) : Real) + (1 / 2 : Real),
            ((x.im : Int) : Real) + (1 / 2 : Real)) ∈
            TileRealization (TileTranslation (TileQuarterTurn T) u) := by
        rw [realization_same]
        exact hxcenter
      exact (center_mem (TileTranslation (TileQuarterTurn T) u) x).mpr hnew
  · intro hempty
    rw [translate.2.1, quarter.2.1]
    dsimp [GaussianTranslation, GaussianQuarterTurn]
    have hcentroid : TileCentroid T =
        ((((T.anchor.re : Int) : Real)), (((T.anchor.im : Int) : Real))) := by
      change (if T.cells.Nonempty then _ else
        ((((T.anchor.re : Int) : Real)), (((T.anchor.im : Int) : Real)))) = _
      rw [ite_eq_right]
      exact Finset.not_nonempty_iff_eq_empty.mpr hempty
    rw [hcentroid] at coordinate_re coordinate_im
    rw [Zsqrtd.ext_iff]
    dsimp at coordinate_re coordinate_im ⊢
    have re_relation : u.re = T.anchor.re + T.anchor.im := by
      exact_mod_cast coordinate_re
    have im_relation : u.im = T.anchor.im - T.anchor.re := by
      exact_mod_cast coordinate_im
    constructor
    · omega
    · omega

end ApollonianSuperharmonic

end
