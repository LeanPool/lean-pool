/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5064T3Rectangles
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.FootprintEdges

-- [TABLET NODE: P5064T3LiteralLocalization]

/-!
# P5064T3LiteralLocalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5064T3LiteralLocalization (P : FordFareyParameter) (hq : 1 < P.q)
    (T : ProtoTile) (t : GaussianInt)
    (hcent : TileCentroid T = TileCentroid (TileTranslation (FordTile P.q) t))
    (S : Fin 3 → Bool → ProtoTile)
    (hS : ∀ i b, BandSubtileOccurrence (FordRecursiveQuadruple P) T i b (S i b)) :
    ∀ i b,
      let U := TileTranslation (P5064T3Rectangles P.q₁ P.q₂ i b) t
      (S i b).cells = U.cells ∧
      ((S i b).cells = ∅ → (S i b).anchor = U.anchor) ∧
      FootprintVertices (S i b) = FootprintVertices U ∧
      FootprintEdges (S i b) = FootprintEdges U ∧
      TileCentroid (S i b) = TileCentroid U := by
-- BODY
  classical
  obtain ⟨_, W, hw, _, hA, hB, hC, hD, hE, haE, hF, haF⟩ :=
    (FordTileRecursiveIdentification P).2.2 hq
  have q1pos : 0 < P.q₁ := by
    by_contra hn
    have hz : P.q₁ = 0 := by omega
    have hd := P.det₁
    simp [hz] at hd
    have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
    have := Int.eq_one_of_dvd_one (by omega) hdv
    omega
  have ne (n : Nat) (hn : 0 < n) : (FordTile n).cells.Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈ ((Finset.range n).product (Finset.range n)).image
      (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
    exact Finset.mem_image.mpr ⟨(0, 0), by simp [hn], rfl⟩
  have n1 := Finset.nonempty_iff_ne_empty.mp (ne P.q₁ q1pos)
  have n2 := Finset.nonempty_iff_ne_empty.mp (ne P.q₂ P.q₂_pos)
  have cells (i : Fin 3) (b : Bool) :
      (W i b).cells = (P5064T3Rectangles P.q₁ P.q₂ i b).cells := by
    fin_cases i <;> cases b <;>
      simp [P5064T3Rectangles, hA, hB, hC, hD, hE, hF]
  have anchors (i : Fin 3) (b : Bool) (he : (W i b).cells = ∅) :
      (W i b).anchor = (P5064T3Rectangles P.q₁ P.q₂ i b).anchor := by
    have hem := (cells i b).symm.trans he
    fin_cases i <;> cases b <;>
      simp [P5064T3Rectangles, TileTranslation, n1, n2] at hem
    · exact haF
    · simpa [P5064T3Rectangles, P.sum_q] using haE
  intro i b
  have hc :
      (TileTranslation (W i b) t).cells =
        (TileTranslation (P5064T3Rectangles P.q₁ P.q₂ i b) t).cells := by
    change (W i b).cells.image _ = (P5064T3Rectangles P.q₁ P.q₂ i b).cells.image _
    rw [cells]
  have ha (he : (TileTranslation (W i b) t).cells = ∅) :
      (TileTranslation (W i b) t).anchor =
        (TileTranslation (P5064T3Rectangles P.q₁ P.q₂ i b) t).anchor := by
    have he' := (TileTranslationFormulas (W i b) t).2.2.1.mp he
    change GaussianTranslation t (W i b).anchor =
      GaussianTranslation t (P5064T3Rectangles P.q₁ P.q₂ i b).anchor
    rw [anchors i b he']
  have hd := (hS i b).2.2.trans (hw i b).2.2.symm
  have hcent' : TileCentroid (S i b) = TileCentroid (TileTranslation (W i b) t) := by
    rw [(TileTranslationFormulas _ _).2.2.2.2.1] at hcent ⊢
    apply Prod.ext
    · have hd1 := congrArg Prod.fst hd
      have hr1 := congrArg Prod.fst hcent
      change (TileCentroid (S i b)).1 - (TileCentroid T).1 =
        (TileCentroid (W i b)).1 - (TileCentroid (FordTile P.q)).1 at hd1
      change (TileCentroid T).1 =
        (TileCentroid (FordTile P.q)).1 + (t.re : Int) at hr1
      change (TileCentroid (S i b)).1 = (TileCentroid (W i b)).1 + (t.re : Int)
      linarith
    · have hd2 := congrArg Prod.snd hd
      have hr2 := congrArg Prod.snd hcent
      change (TileCentroid (S i b)).2 - (TileCentroid T).2 =
        (TileCentroid (W i b)).2 - (TileCentroid (FordTile P.q)).2 at hd2
      change (TileCentroid T).2 =
        (TileCentroid (FordTile P.q)).2 + (t.im : Int) at hr2
      change (TileCentroid (S i b)).2 = (TileCentroid (W i b)).2 + (t.im : Int)
      linarith
  have hu := BandPrototileCentroidUnique _ _ _ (hS i b).1
    (BandPrototileTranslation _ _ t (hw i b).1) hcent'
  have finalCells := hu.1.trans hc
  have finalAnchor (he : (S i b).cells = ∅) :
      (S i b).anchor =
        (TileTranslation (P5064T3Rectangles P.q₁ P.q₂ i b) t).anchor :=
    (hu.2 he).trans (ha (hu.1.symm.trans he))
  have obs := ProtoTileObservableExtensionality _ _ finalCells finalAnchor
  refine ⟨finalCells, finalAnchor, obs.1, ?_, obs.2.2.2.2⟩
  simp only [FootprintEdges]
  rw [finalCells]

end ApollonianSuperharmonic

end
