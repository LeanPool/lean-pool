/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.TileOdometerCentralSymmetry
public import LeanPool.ApollonianSuperharmonic.TileStringCentralCovariance

-- [TABLET NODE: OdometerStringRespectCentralCovariance]

/-!
# OdometerStringRespectCentralCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem OdometerStringRespectCentralCovariance
    (C : BandCircle) (orientation : Bool)
    (base R S : ProtoTile) (tiles : List ProtoTile)
    (hs gs : List PartialOdometer) (u a : GaussianInt)
    (hrespect : OdometerStringRespect C orientation base R S tiles hs)
    (htransform : List.Forall₂ (fun h g => exists b : Int,
      g = PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) u a b)
      hs gs) :
    OdometerStringRespect C orientation
      (TileTranslation (TileHalfTurn base) u)
      (TileTranslation (TileHalfTurn R) u)
      (TileTranslation (TileHalfTurn S) u)
      (tiles.map (fun T => TileTranslation (TileHalfTurn T) u)) gs := by
-- BODY
  classical
  have transportAdjacent (T T' : ProtoTile) (h h' : PartialOdometer)
      (hadj : LeftLatticeAdjacent C T T' h h') (b b' : Int) :
      LeftLatticeAdjacent C
        (TileTranslation (TileHalfTurn T) u)
        (TileTranslation (TileHalfTurn T') u)
        (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) u a b)
        (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h') u a b') := by
    rcases hadj with ⟨hO, hO', ⟨p, p', hp, hp', hshape⟩⟩
    have hnew : TileOdometer C.1.1
        (TileTranslation (TileHalfTurn T) u)
        (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) u a b) :=
      TileOdometerAffineTranslation C.1.1 (TileHalfTurn T)
        (PartialOdometerHalfTurn h) u a b
        (TileOdometerCentralSymmetry C.1.1 T h hO).1
    have hnew' : TileOdometer C.1.1
        (TileTranslation (TileHalfTurn T') u)
        (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h') u a b') :=
      TileOdometerAffineTranslation C.1.1 (TileHalfTurn T')
        (PartialOdometerHalfTurn h') u a b'
        (TileOdometerCentralSymmetry C.1.1 T' h' hO').1
    have hs : PartialOdometerSlope
        (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) u a b) =
        some (-p.1 + (a.re : ℝ), -p.2 + (a.im : ℝ)) := by
      have ha := (PartialOdometerAffineTranslateFormulas
        (PartialOdometerHalfTurn h) u a b).2.2.2.2.2
      have hh := (PartialOdometerHalfTurnFormulas h).2.2.2.2.2.2
      rw [ha, hh, hp]
      rfl
    have hs' : PartialOdometerSlope
        (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h') u a b') =
        some (-p'.1 + (a.re : ℝ), -p'.2 + (a.im : ℝ)) := by
      have ha := (PartialOdometerAffineTranslateFormulas
        (PartialOdometerHalfTurn h') u a b').2.2.2.2.2
      have hh := (PartialOdometerHalfTurnFormulas h').2.2.2.2.2.2
      rw [ha, hh, hp']
      rfl
    have hcent : TileCentroid (TileTranslation (TileHalfTurn T') u) -
        TileCentroid (TileTranslation (TileHalfTurn T) u) =
        -(TileCentroid T' - TileCentroid T) := by
      rw [(TileTranslationFormulas (TileHalfTurn T') u).2.2.2.2.1,
        (TileTranslationFormulas (TileHalfTurn T) u).2.2.2.2.1]
      rw [(TileHalfTurnFormulas T').2.2.2.2.2.2.2.1,
        (TileHalfTurnFormulas T).2.2.2.2.2.2.2.1]
      ext <;> dsimp <;> ring
    refine ⟨hnew, hnew', ?_⟩
    refine ⟨(-p.1 + (a.re : ℝ), -p.2 + (a.im : ℝ)),
      (-p'.1 + (a.re : ℝ), -p'.2 + (a.im : ℝ)), hs, hs', ?_⟩
    rcases hshape with hunit | hnon
    · left
      rcases hunit with ⟨hor, orig, v, hv, hct, hx, hy⟩
      refine ⟨hor, orig, -v, ?_, ?_, ?_, ?_⟩
      · cases orig <;> simp only [UnitTriangularStep, Bool.false_eq_true, ↓reduceIte,
          Int.reduceNeg, neg_add_rev, neg_neg, Finset.mem_insert, Finset.mem_singleton] at hv
        all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [UnitTriangularStep]
      · rw [hcent]
        rw [hct]
        ext <;> simp [GaussianRealPoint]
      · dsimp
        simp only [Int.cast_neg]
        ring_nf
        linear_combination -hx
      · dsimp
        simp only [Int.cast_neg]
        ring_nf
        linear_combination -hy
    · right
      rcases hnon with ⟨q, i, e, hq, hq0, hct, hx, hy⟩
      refine ⟨q, i, !e, hq, hq0, ?_, ?_, ?_⟩
      · rw [hcent, hct]
        by_cases he : e = true <;> simp [he]
      · dsimp
        by_cases he : e = true <;> simp [he] at hx ⊢ <;> linarith
      · dsimp
        by_cases he : e = true <;> simp [he] at hy ⊢ <;> linarith
  rcases hrespect with ⟨hstring, htiles, hchain⟩
  have savedString := hstring
  clear hstring
  revert hchain savedString htiles
  have tileTransport : ∀ {ts : List ProtoTile},
        List.Forall₂ (fun T h => TileOdometer C.1.1 T h) ts hs →
        List.Forall₂ (fun T h => TileOdometer C.1.1 T h) (ts.map
            (fun T => TileTranslation (TileHalfTurn T) u)) gs := by
      intro ts ho
      revert ho
      induction htransform generalizing ts with
      | nil => intro ho; cases ho; exact .nil
      | @cons h g hs gs hex rest ih =>
        intro ho
        cases ho with
        | cons hto hor =>
          rcases hex with ⟨b, rfl⟩
          exact .cons (TileOdometerAffineTranslation C.1.1
            (TileHalfTurn _) (PartialOdometerHalfTurn h) u a b
            (TileOdometerCentralSymmetry C.1.1 _ h hto).1) (ih hor)
      /- induction ho generalizing gs with
      | nil => cases htransform; exact .nil
      | cons hto hor ih =>
        cases htransform with
        | cons hex rest =>
          rcases hex with ⟨b, rfl⟩
          exact .cons (TileOdometerAffineTranslation C.1.1
            (TileHalfTurn _) (PartialOdometerHalfTurn _) u a b
            (TileOdometerCentralSymmetry C.1.1 _ _ hto).1) (ih (gs := _) rest hor) -/
  intro htiles hchain savedString
  refine ⟨TileStringCentralCovariance C orientation base R S tiles u savedString, tileTransport
      htiles, ?_⟩
  have chainTransport : ∀ {hs gs : List PartialOdometer} {ts : List ProtoTile},
        List.Forall₂ (fun h g => ∃ b : Int,
          g = PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) u a b) hs gs →
        List.Forall₂ (fun T h => TileOdometer C.1.1 T h) ts hs →
        List.IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2) (ts.zip hs) →
        List.IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)
          ((ts.map (fun T => TileTranslation (TileHalfTurn T) u)).zip gs) := by
      intro hs gs ts ht
      revert ts
      induction ht with
      | nil =>
        intro ts ho hc
        cases ho
        exact .nil
      | @cons h g hs gs hex rest ih =>
        intro ts ho hc
        cases ts with
        | nil => cases ho
        | cons t ts =>
          cases ho with
          | cons hto hor =>
            cases ts with
            | nil => exact .singleton _
            | cons t' ts' =>
              cases rest with
              | nil => cases hor
              | cons hrest rest =>
                cases hor with
                | cons hto' hor =>
                  cases hc with
                  | cons_cons hadj htail =>
                    rcases hex with ⟨b, rfl⟩
                    rcases hrest with ⟨b', rfl⟩
                    exact .cons_cons (transportAdjacent _ _ _ _ hadj b b')
                      (ih (List.Forall₂.cons hto' hor) htail)
  exact chainTransport htransform htiles hchain

end ApollonianSuperharmonic

end
