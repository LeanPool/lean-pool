/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AncestorTile
public import LeanPool.ApollonianSuperharmonic.TileHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: AncestorTileCentralCovariance]

/-!
# AncestorTileCentralCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem AncestorTileCentralCovariance
    (C C' : CircleCoordinates) (T T' : ProtoTile) (u : GaussianInt)
    (hancestor : AncestorTile C C' T T') :
    AncestorTile C C'
      (TileTranslation (TileHalfTurn T) u)
      (TileTranslation (TileHalfTurn T') u) := by
-- BODY
  unfold AncestorTile at hancestor ⊢
  let transform : ProtoTile → ProtoTile :=
    fun V => TileTranslation (TileHalfTurn V) u
  have centroid_transform : ∀ V : ProtoTile,
      TileCentroid (transform V) =
        (-(TileCentroid V).1 + (u.re : Real),
         -(TileCentroid V).2 + (u.im : Real)) := by
    intro V
    dsimp [transform]
    rw [(TileTranslationFormulas (TileHalfTurn V) u).2.2.2.2.1,
      (TileHalfTurnFormulas V).2.2.2.2.2.2.2.1]
  have footprint_transform : ∀ V : ProtoTile,
      FootprintVertices (transform V) =
        GaussianTranslation u '' ((fun x : GaussianInt => -x) ''
          FootprintVertices V) := by
    intro V
    dsimp [transform]
    rw [(TileTranslationFormulas (TileHalfTurn V) u).2.2.2.2.2.1,
      (TileHalfTurnFormulas V).2.2.2.2.2.2.1]
  have band_transform : ∀ (D : CircleCoordinates) (V : ProtoTile),
      BandPrototile D V → BandPrototile D (transform V) := by
    intro D V hV
    induction hV with
    | line w x hw =>
        apply BandPrototile.line
        exact hw
    | unit z x =>
        apply BandPrototile.unit
    | @decompose q hq S V hS hcells hfoot hcentroid ih =>
        let R : Fin 3 → Bool → ProtoTile :=
          fun i s => transform (S i (!s))
        have hR : ∀ i s, BandPrototile (q i.succ) (R i s) := by
          intro i s
          exact ih i (!s)
        apply BandPrototile.decompose hq hR
        · intro x
          constructor
          · intro hx
            dsimp [transform, TileTranslation, TileHalfTurn] at hx
            rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
            rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
            rcases (hcells y).mp hy with ⟨i, s, hs⟩
            refine ⟨i, !s, ?_⟩
            dsimp [R]
            simp only [Bool.not_not]
            change GaussianTranslation u (-y - 1 - ⟨0, 1⟩) ∈
              (transform (S i s)).cells
            change GaussianTranslation u (-y - 1 - ⟨0, 1⟩) ∈
              (TileTranslation (TileHalfTurn (S i s)) u).cells
            exact Finset.mem_image.mpr ⟨-y - 1 - ⟨0, 1⟩,
              Finset.mem_image.mpr ⟨y, hs, rfl⟩, rfl⟩
          · rintro ⟨i, s, hs⟩
            have hs' : x ∈ (transform (S i (!s))).cells := hs
            have hx' : x ∈ (transform V).cells := by
              dsimp [transform, TileTranslation, TileHalfTurn]
              rcases Finset.mem_image.mp hs' with ⟨z, hz, heq⟩
              rcases Finset.mem_image.mp hz with ⟨y, hy, heq'⟩
              exact Finset.mem_image.mpr ⟨z,
                Finset.mem_image.mpr ⟨y, (hcells y).mpr ⟨i, !s, hy⟩, heq'⟩,
                heq⟩
            exact hx'
        · intro i s
          rw [footprint_transform, footprint_transform]
          intro x hx
          rcases hx with ⟨y, ⟨v, hv, rfl⟩, rfl⟩
          refine ⟨-v, ⟨v, hfoot i (!s) hv, rfl⟩, rfl⟩
        · intro i s
          have hp := hcentroid i (!s)
          rw [centroid_transform, centroid_transform]
          have hfirst := congrArg Prod.fst hp
          have hsecond := congrArg Prod.snd hp
          have hsign :
              (if (!s) = true then (1 : Real) else -1) =
                -(if s = true then (1 : Real) else -1) := by
            cases s <;> norm_num
          rw [hsign] at hfirst hsecond
          dsimp [R, transform] at hfirst hsecond ⊢
          dsimp [GaussianRealPoint] at hfirst hsecond ⊢
          ring_nf at hfirst hsecond ⊢
          apply Prod.ext
          all_goals try dsimp at *
          all_goals linarith
  have transformed_link : ∀ X Y : CircleCoordinates × ProtoTile,
      (∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
        ProperBandQuadruple q ∧ q 0 = Y.1 ∧ q i.succ = X.1 ∧
        BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
        FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
        TileCentroid X.2 - TileCentroid Y.2 =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).1)))) →
      (∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
        ProperBandQuadruple q ∧ q 0 = Y.1 ∧ q i.succ = X.1 ∧
        BandPrototile Y.1 (transform Y.2) ∧ BandPrototile X.1 (transform X.2) ∧
        FootprintVertices (transform X.2) ⊆ FootprintVertices (transform Y.2) ∧
        TileCentroid (transform X.2) - TileCentroid (transform Y.2) =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).1)))) := by
    intro X Y h
    rcases h with ⟨q, i, s, hq, hq0, hqi, hY, hX, hfoot, hcent⟩
    refine ⟨q, i, !s, hq, hq0, hqi, band_transform _ _ hY,
      band_transform _ _ hX, ?_, ?_⟩
    · rw [footprint_transform, footprint_transform]
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      rcases hw with ⟨v, hv, rfl⟩
      exact ⟨-v, ⟨v, hfoot hv, by simp⟩, rfl⟩
    · rw [centroid_transform, centroid_transform]
      have hfirst := congrArg Prod.fst hcent
      have hsecond := congrArg Prod.snd hcent
      dsimp [GaussianRealPoint] at hfirst hsecond ⊢
      rcases s with _ | _ <;> simp at * <;> constructor <;> linarith
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ =>
      Relation.ReflTransGen
        (fun X Y : CircleCoordinates × ProtoTile =>
          ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
            ProperBandQuadruple q ∧ q 0 = Y.1 ∧ q i.succ = X.1 ∧
            BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
            FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
            TileCentroid X.2 - TileCentroid Y.2 =
              (if s = true then (1 : Real) else -1) •
                ((1 / 2 : Real) •
                  (GaussianRealPoint
                      (BandVectors.1 (q ((i + 2).succ))
                        (q ((i + 1).succ))) -
                    (-((GaussianRealPoint
                        (BandVectors.1 (q ((i + 2).succ))
                          (q ((i + 1).succ)))).2),
                      (GaussianRealPoint
                        (BandVectors.1 (q ((i + 2).succ))
                          (q ((i + 1).succ)))).1))))
        (a.1, transform a.2) (C', transform T')) hancestor
    ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a c hedge hrest ih
    exact Relation.ReflTransGen.head (transformed_link a c hedge) ih

end ApollonianSuperharmonic

end
