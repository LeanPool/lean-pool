/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototileCentralSymmetry
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.TileArea
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: BandSignedOccurrenceHalfTurn]

/-!
# BandSignedOccurrenceHalfTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandSignedOccurrenceHalfTurn (q : Fin 4 → CircleCoordinates)
    (x : Real × Real) (S : Fin 3 → Bool → ProtoTile)
    (hS : ∀ i s, BandPrototile (q i.succ) (S i s))
    (hcent : ∀ i s,
      TileCentroid (S i s) - x =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint
                (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
              (-((GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).2),
                (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).1)))) :
    ∀ i : Fin 3,
      let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
      let u := GaussianQuarterTurn w - w
      (TileTranslation (S i true) u).cells = (S i false).cells ∧
      ((S i true).cells = ∅ →
        (TileTranslation (S i true) u).anchor = (S i false).anchor) ∧
      FootprintVertices (TileTranslation (S i true) u) =
        FootprintVertices (S i false) ∧
      TileCentroid (TileTranslation (S i true) u) =
        TileCentroid (S i false) ∧
      TileArea (S i true) = TileArea (S i false) ∧
      CentrallyReflectedAt x (S i true) (S i false) := by
-- BODY
  intro i
  dsimp
  let w := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
  let u := GaussianQuarterTurn w - w
  have hplus := hcent i true
  have hminus := hcent i false
  have hu_re : (u.re : Real) =
      -(GaussianRealPoint w).1 - (GaussianRealPoint w).2 := by
    change (((-w.im - w.re : Int) : Real)) =
      -((w.re : Int) : Real) - ((w.im : Int) : Real)
    norm_num
    ring
  have hu_im : (u.im : Real) =
      (GaussianRealPoint w).1 - (GaussianRealPoint w).2 := by
    change (((w.re - w.im : Int) : Real)) =
      ((w.re : Int) : Real) - ((w.im : Int) : Real)
    norm_num
  have hurexp : (u.re : Real) =
      -((BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))).re : Real) -
        ((BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))).im : Real) := by
    simpa [w, GaussianRealPoint] using hu_re
  have huimexp : (u.im : Real) =
      ((BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))).re : Real) -
        ((BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))).im : Real) := by
    simpa [w, GaussianRealPoint] using hu_im
  have hcentroid :
      TileCentroid (TileTranslation (S i true) u) = TileCentroid (S i false) := by
    rw [(TileTranslationFormulas (S i true) u).2.2.2.2.1]
    have hre := congrArg Prod.fst hplus
    have him := congrArg Prod.snd hplus
    have hrem := congrArg Prod.fst hminus
    have himm := congrArg Prod.snd hminus
    dsimp [w] at hre him hrem himm
    dsimp [w, GaussianRealPoint] at hu_re hu_im
    have hre' : (TileCentroid (S i true)).1 - x.1 =
        (1 / 2 : Real) *
          (((w.re : Int) : Real) + ((w.im : Int) : Real)) := by
      simpa [w, GaussianRealPoint] using hre
    have him' : (TileCentroid (S i true)).2 - x.2 =
        (1 / 2 : Real) *
          (((w.im : Int) : Real) - ((w.re : Int) : Real)) := by
      simpa [w, GaussianRealPoint] using him
    have hrem' : (TileCentroid (S i false)).1 - x.1 =
        -(1 / 2 : Real) *
          (((w.re : Int) : Real) + ((w.im : Int) : Real)) := by
      simpa [w, GaussianRealPoint] using hrem
    have himm' : (TileCentroid (S i false)).2 - x.2 =
        -(1 / 2 : Real) *
          (((w.im : Int) : Real) - ((w.re : Int) : Real)) := by
      simpa [w, GaussianRealPoint] using himm
    apply Prod.ext
    · change (TileCentroid (S i true)).1 + (u.re : Real) = _
      rw [hu_re]
      linarith [hrem']
    · change (TileCentroid (S i true)).2 + (u.im : Real) = _
      rw [hu_im]
      linarith [himm']
  have htranslated :
      BandPrototile (q i.succ) (TileTranslation (S i true) u) := by
    exact BandPrototileTranslation (q i.succ) (S i true) u (hS i true)
  have unique := BandPrototileCentroidUnique (q i.succ)
    (TileTranslation (S i true) u) (S i false) htranslated (hS i false) hcentroid
  have hcells : (TileTranslation (S i true) u).cells = (S i false).cells := unique.1
  have hempty : (S i true).cells = ∅ →
      (TileTranslation (S i true) u).anchor = (S i false).anchor := by
    intro h
    exact unique.2 ((TileTranslationFormulas (S i true) u).2.2.1.mpr h)
  have hfoot : FootprintVertices (TileTranslation (S i true) u) =
      FootprintVertices (S i false) := by
    by_cases h : (S i true).cells = ∅
    · have hf : (S i false).cells = ∅ := by
        rw [← hcells]
        exact (TileTranslationFormulas (S i true) u).2.2.1.mpr h
      have ht0 : (TileTranslation (S i true) u).cells = ∅ :=
        (TileTranslationFormulas (S i true) u).2.2.1.mpr h
      simp [FootprintVertices, ht0, hf, hempty h]
    · have ht : (TileTranslation (S i true) u).cells.Nonempty := by
        rw [hcells]
        have htne : (TileTranslation (S i true) u).cells ≠ ∅ :=
          (TileTranslationFormulas (S i true) u).2.2.1.not.mpr h
        exact Finset.nonempty_iff_ne_empty.mpr (by
          rw [← hcells]
          exact htne)
      have hfne : (S i false).cells.Nonempty := hcells ▸ ht
      rw [FootprintVertices, FootprintVertices]
      simp only [ite_eq_left ht, ite_eq_left hfne]
      simp [hcells]
  have harea : TileArea (S i true) = TileArea (S i false) := by
    dsimp [TileArea]
    rw [← hcells, (TileTranslationFormulas (S i true) u).1]
    symm
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have hre := congrArg Zsqrtd.re hab
    have him := congrArg Zsqrtd.im hab
    dsimp [GaussianTranslation] at hre him
    apply Zsqrtd.ext_iff.mpr
    exact ⟨by omega, by omega⟩
  have hcentral : CentrallyReflectedAt (TileCentroid (S i true))
      (S i true) (S i true) :=
    BandPrototileCentralSymmetry (q i.succ) (S i true) (hS i true)
  have hreal : TileRealization (TileTranslation (S i true) u) =
      TileRealization (S i false) := by
    rw [TileRealization, hcells, TileRealization]
  have hreflect : CentrallyReflectedAt x (S i true) (S i false) := by
    rw [CentrallyReflectedAt, ← hreal,
      (TileTranslationFormulas (S i true) u).2.2.2.1]
    nth_rewrite 1 [hcentral]
    rw [Set.image_image]
    have map_eq :
        (fun z : Real × Real =>
          ((2 * (TileCentroid (S i true)).1 - z.1, 2 * (TileCentroid (S i true)).2 - z.2).1 +
              (u.re : Real),
            (2 * (TileCentroid (S i true)).1 - z.1, 2 * (TileCentroid (S i true)).2 - z.2).2 +
                (u.im : Real))) =
          (fun z : Real × Real => (2 * x.1 - z.1, 2 * x.2 - z.2)) := by
      funext z
      apply Prod.ext
      · dsimp
        rw [hurexp]
        have hx := congrArg Prod.fst hplus
        have hr := congrArg Prod.fst hminus
        dsimp [w, GaussianRealPoint] at hx hr ⊢
        ring_nf at hx hr ⊢
        linarith
      · dsimp
        rw [huimexp]
        have hy := congrArg Prod.snd hplus
        have hi := congrArg Prod.snd hminus
        dsimp [w, GaussianRealPoint] at hy hi ⊢
        ring_nf at hy hi ⊢
        linarith
    rw [map_eq]
  exact ⟨hcells, hempty, hfoot, hcentroid, harea, hreflect⟩

end ApollonianSuperharmonic

end
