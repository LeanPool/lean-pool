/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOdometerRowData
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality

-- [TABLET NODE: P5472T1LiteralFordPlacement]

/-!
# P5472T1LiteralFordPlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LiteralFordPlacementGeometry

private theorem hplus' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (r : Fin 3 → Bool
            → PartialOdometer), ∀ (Q : Fin 3 → Bool → ProtoTile), ∀ (S : Fin 3 → Bool →
            ProtoTile), ∀ (u : Fin 3 → Bool → PartialOdometer), ∀ (v : Fin 3 → Bool →
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → (∀ (F :
            FordFareyParameter), ∀ (s : BandPackingSymmetry), ∀ (delta : Bool),
            (BandPackingSymmetryCircleAction s (q (1 : Fin (4 : ℕ))) = FordCircleCoordinate F.p
            F.q) → (
        let c := BandPackingSymmetryVectorAction s x
        let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
        let hp := PartialOdometerAffineTranslate
          (BandPackingSymmetryPartialOdometerAction s (r 0 (!delta))) (-c) 0 0
        TileOdometer (FordCircleCoordinate F.p F.q) U hp)) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data F s delta hrootCircle c U hp
  have hc := (BandPackingSymmetryTileOdometerCovariance s (q 1)
    (P 0 (!delta)) (r 0 (!delta)) (data.hP 0 (!delta))).1
  rw [hrootCircle] at hc
  simpa [U, hp, c] using
    TileOdometerAffineTranslation _ _ _ _ _ _ hc

private theorem hminus' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (r : Fin 3 → Bool
            → PartialOdometer), ∀ (Q : Fin 3 → Bool → ProtoTile), ∀ (S : Fin 3 → Bool →
            ProtoTile), ∀ (u : Fin 3 → Bool → PartialOdometer), ∀ (v : Fin 3 → Bool →
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → (∀ (F :
            FordFareyParameter), ∀ (s : BandPackingSymmetry), ∀ (delta : Bool),
            (BandPackingSymmetryCircleAction s (q (1 : Fin (4 : ℕ))) = FordCircleCoordinate F.p
            F.q) → (
        let c := BandPackingSymmetryVectorAction s x
        let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
        let hm := PartialOdometerAffineTranslate
          (BandPackingSymmetryPartialOdometerAction s (r 0 delta)) (-c) 0 0
        TileOdometer (FordCircleCoordinate F.p F.q) V hm)) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data F s delta hrootCircle c V hm
  have hc := (BandPackingSymmetryTileOdometerCovariance s (q 1)
    (P 0 delta) (r 0 delta) (data.hP 0 delta)).1
  rw [hrootCircle] at hc
  simpa [V, hm, c] using
    TileOdometerAffineTranslation _ _ _ _ _ _ hc

private theorem hocc :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (r : Fin 3 → Bool
            → PartialOdometer), ∀ (Q : Fin 3 → Bool → ProtoTile), ∀ (S : Fin 3 → Bool →
            ProtoTile), ∀ (u : Fin 3 → Bool → PartialOdometer), ∀ (v : Fin 3 → Bool →
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (i : Fin 3), ∀ (b : Bool),
            BandSubtileOccurrence q T i b (P i b)) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data i b
  refine ⟨TileOdometerBandPrototile _ _ _ (data.hP i b), data.hPfoot i b, ?_⟩
  exact data.hPcent i b

private theorem hePlus :
    (by
      classical
      exact
        ∀ (s : BandPackingSymmetry), ∀ (delta : Bool), (BandPackingSymmetryReversesOrientation s
            = false) → (∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), (∀ (i : Fin (3 : ℕ)), ∀
            (s_1 : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s_1) = ((fun (i : Fin
            (3 : ℕ)) => if BandPackingSymmetryReversesOrientation s = true then -i else i) i, s_1
            ^^ delta)) → (e (0, !delta) = (0, true))) ) := by
  classical
  intro s delta hrev e he
  have hh := he 0 (!delta)
  simpa [hrev] using hh

private theorem heMinus :
    (by
      classical
      exact
        ∀ (s : BandPackingSymmetry), ∀ (delta : Bool), (BandPackingSymmetryReversesOrientation s
            = false) → (∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), (∀ (i : Fin (3 : ℕ)), ∀
            (s_1 : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s_1) = ((fun (i : Fin
            (3 : ℕ)) => if BandPackingSymmetryReversesOrientation s = true then -i else i) i, s_1
            ^^ delta)) → (e (0, delta) = (0, false))) ) := by
  classical
  intro s delta hrev e he
  have hh := he 0 delta
  simpa [hrev] using hh

private theorem hPplusCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (P : Fin 3 → Bool → ProtoTile), ∀
            (s : BandPackingSymmetry), ∀ (delta : Bool), ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ)
            × Bool), ∀ (P' : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s_1 :
            Bool), P' ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s_1)).1 ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s_1)).2 = BandPackingSymmetryTileAction s (P i
            s_1)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s_1 : Bool), BandSubtileOccurrence
            (BandPackingSymmetryQuadrupleAction s q) (BandPackingSymmetryTileAction s T) i s_1
            (P' i s_1)) → ((e (0, !delta) = (0, true)) → (TileCentroid
            (BandPackingSymmetryTileAction s (P 0 (!delta))) - TileCentroid
            (BandPackingSymmetryTileAction s T) = (1 : Real) • ((1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2)) - (-(GaussianRealPoint (BandVectors.1
            (BandPackingSymmetryQuadrupleAction s q 3) (BandPackingSymmetryQuadrupleAction s q
            2))).2, (GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2))).1)))))) ) := by
  classical
  intro q T P s delta e P' hPmap hPocc hePlus
  have hh := (hPocc 0 true).2.2
  have hm := hPmap 0 (!delta)
  have hm' : P' 0 true = BandPackingSymmetryTileAction s (P 0 (!delta)) := by
    simpa [hePlus] using hm
  rw [hm'] at hh
  simpa [BandSubtileOccurrence] using hh

private theorem hPminusCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (P : Fin 3 → Bool → ProtoTile), ∀
            (s : BandPackingSymmetry), ∀ (delta : Bool), ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ)
            × Bool), ∀ (P' : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s_1 :
            Bool), P' ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s_1)).1 ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s_1)).2 = BandPackingSymmetryTileAction s (P i
            s_1)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s_1 : Bool), BandSubtileOccurrence
            (BandPackingSymmetryQuadrupleAction s q) (BandPackingSymmetryTileAction s T) i s_1
            (P' i s_1)) → ((e (0, delta) = (0, false)) → (TileCentroid
            (BandPackingSymmetryTileAction s (P 0 delta)) - TileCentroid
            (BandPackingSymmetryTileAction s T) = (-1 : Real) • ((1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2)) - (-(GaussianRealPoint (BandVectors.1
            (BandPackingSymmetryQuadrupleAction s q 3) (BandPackingSymmetryQuadrupleAction s q
            2))).2, (GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2))).1)))))) ) := by
  classical
  intro q T P s delta e P' hPmap hPocc heMinus
  have hh := (hPocc 0 false).2.2
  have hm := hPmap 0 delta
  have hm' : P' 0 false = BandPackingSymmetryTileAction s (P 0 delta) := by
    simpa [heMinus] using hm
  rw [hm'] at hh
  simpa [BandSubtileOccurrence] using hh

private theorem hcenter' :
    (by
      classical
        exact
        ∀ (T : ProtoTile),
          ∀ (x : GaussianInt),
            (GaussianRealPoint x = TileCentroid T) →
              (∀ (s : BandPackingSymmetry),
                ((∃ (z : GaussianInt),
                    s = BandPackingSymmetry.shift z ∨
                      s =
                        (BandPackingSymmetry.shift z).comp
                          BandPackingSymmetry.negate) →
                  (let c := BandPackingSymmetryVectorAction s x;
                  (TileCentroid (BandPackingSymmetryTileAction s T) =
                    GaussianRealPoint c))))) := by
  classical
  intro T x hcenter s hword c
  rcases hword with ⟨w, hs | hs⟩
  · subst s
    simpa [c, BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction] using
      hcenter.symm
  · subst s
    change TileCentroid (TileQuarterTurn T) =
      GaussianRealPoint (GaussianQuarterTurn x)
    rw [(TileQuarterTurnFormulas T).2.2.2.2.1]
    have hh := congrArg (fun p : Real × Real => (-p.2, p.1)) hcenter
    simpa [GaussianRealPoint, GaussianQuarterTurn] using hh.symm

private theorem hDplus :
    (by
      classical
      exact
        ∀ (F : FordFareyParameter), ((F.q : Real) = (F.q₁ : Real) + F.q₂) → ((1 : Real) • ((1 / 2
            : Real) • (GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt) -
            (-(GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt)).2,
            (GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt)).1))) = (((F.q₂ :
            Real) - F.q₁) / 2, (F.q : Real) / 2)) ) := by
  classical
  intro F hsumReal
  ext <;> simp [GaussianRealPoint]  <;> linarith

private theorem hDminus :
    (by
      classical
      exact
        ∀ (F : FordFareyParameter), ((F.q : Real) = (F.q₁ : Real) + F.q₂) → ((-1 : Real) • ((1 /
            2 : Real) • (GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt) -
            (-(GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt)).2,
            (GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt)).1))) = (-((F.q₂ :
            Real) - F.q₁) / 2, -(F.q : Real) / 2)) ) := by
  classical
  intro F hsumReal
  ext <;> simp [GaussianRealPoint]  <;> linarith

private theorem hUcent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (P : Fin 3 → Bool → ProtoTile), ∀
            (x : GaussianInt), ∀ (F : FordFareyParameter), ∀ (s : BandPackingSymmetry), ∀ (delta
            : Bool), (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q (3 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction s q (2 : Fin (4 : ℕ))) = (⟨-(↑F.q₁ : ℤ), (↑F.q₂ :
            ℤ)⟩ : GaussianInt)) → (
        let c := BandPackingSymmetryVectorAction s x
        let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
        (TileCentroid (BandPackingSymmetryTileAction s (P 0 (!delta))) - TileCentroid
            (BandPackingSymmetryTileAction s T) = (1 : Real) • ((1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2)) - (-(GaussianRealPoint (BandVectors.1
            (BandPackingSymmetryQuadrupleAction s q 3) (BandPackingSymmetryQuadrupleAction s q
            2))).2, (GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2))).1)))) → ((TileCentroid
            (BandPackingSymmetryTileAction s T) = GaussianRealPoint c) → (((1 : Real) • ((1 / 2 :
            Real) • (GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt) -
            (-(GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt)).2,
            (GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt)).1))) = (((F.q₂ :
            Real) - F.q₁) / 2, (F.q : Real) / 2)) → (TileCentroid U = (((F.q₂ : Real) - F.q₁) /
            2, (F.q : Real) / 2))))) ) := by
  classical
  intro q T P x F s delta hW c U hPplusCent hcenter' hDplus
  have hh := hPplusCent
  rw [hW, hcenter'] at hh
  rw [(TileTranslationFormulas
    (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)).2.2.2.2.1]
  change TileCentroid (BandPackingSymmetryTileAction s (P 0 (!delta))) +
      GaussianRealPoint (-c) = _
  have hsub := hh
  rw [hDplus] at hsub
  have hsub1 : (TileCentroid (BandPackingSymmetryTileAction s (P 0 (!delta)))).1 -
      (c.re : Real) = ((F.q₂ : Real) - F.q₁) / 2 := by
    simpa [GaussianRealPoint] using congrArg Prod.fst hsub
  have hsub2 : (TileCentroid (BandPackingSymmetryTileAction s (P 0 (!delta)))).2 -
      (c.im : Real) = (F.q : Real) / 2 := by
    simpa [GaussianRealPoint] using congrArg Prod.snd hsub
  have heq : TileCentroid (BandPackingSymmetryTileAction s (P 0 (!delta))) =
      GaussianRealPoint c +
        (((F.q₂ : Real) - F.q₁) / 2, (F.q : Real) / 2) := by
    apply Prod.ext
    · change (TileCentroid (BandPackingSymmetryTileAction s (P 0 (!delta)))).1 =
        (c.re : Real) + ((F.q₂ : Real) - F.q₁) / 2
      linarith
    · change (TileCentroid (BandPackingSymmetryTileAction s (P 0 (!delta)))).2 =
        (c.im : Real) + (F.q : Real) / 2
      linarith
  rw [heq]
  ext <;> simp [GaussianRealPoint]

private theorem hVcent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (P : Fin 3 → Bool → ProtoTile), ∀
            (x : GaussianInt), ∀ (F : FordFareyParameter), ∀ (s : BandPackingSymmetry), ∀ (delta
            : Bool), (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q (3 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction s q (2 : Fin (4 : ℕ))) = (⟨-(↑F.q₁ : ℤ), (↑F.q₂ :
            ℤ)⟩ : GaussianInt)) → (
        let c := BandPackingSymmetryVectorAction s x
        let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
        (TileCentroid (BandPackingSymmetryTileAction s (P 0 delta)) - TileCentroid
            (BandPackingSymmetryTileAction s T) = (-1 : Real) • ((1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2)) - (-(GaussianRealPoint (BandVectors.1
            (BandPackingSymmetryQuadrupleAction s q 3) (BandPackingSymmetryQuadrupleAction s q
            2))).2, (GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2))).1)))) → ((TileCentroid
            (BandPackingSymmetryTileAction s T) = GaussianRealPoint c) → (((-1 : Real) • ((1 / 2
            : Real) • (GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt) -
            (-(GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt)).2,
            (GaussianRealPoint (⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ : GaussianInt)).1))) = (-((F.q₂ :
            Real) - F.q₁) / 2, -(F.q : Real) / 2)) → (TileCentroid V = (-((F.q₂ : Real) - F.q₁) /
            2, -(F.q : Real) / 2))))) ) := by
  classical
  intro q T P x F s delta hW c V hPminusCent hcenter' hDminus
  have hh := hPminusCent
  rw [hW, hcenter'] at hh
  rw [(TileTranslationFormulas
    (BandPackingSymmetryTileAction s (P 0 delta)) (-c)).2.2.2.2.1]
  change TileCentroid (BandPackingSymmetryTileAction s (P 0 delta)) +
      GaussianRealPoint (-c) = _
  have hsub := hh
  rw [hDminus] at hsub
  have hsub1 : (TileCentroid (BandPackingSymmetryTileAction s (P 0 delta))).1 -
      (c.re : Real) = -((F.q₂ : Real) - F.q₁) / 2 := by
    simpa [GaussianRealPoint] using congrArg Prod.fst hsub
  have hsub2 : (TileCentroid (BandPackingSymmetryTileAction s (P 0 delta))).2 -
      (c.im : Real) = -(F.q : Real) / 2 := by
    simpa [GaussianRealPoint] using congrArg Prod.snd hsub
  have heq : TileCentroid (BandPackingSymmetryTileAction s (P 0 delta)) =
      GaussianRealPoint c +
        (-((F.q₂ : Real) - F.q₁) / 2, -(F.q : Real) / 2) := by
    apply Prod.ext
    · change (TileCentroid (BandPackingSymmetryTileAction s (P 0 delta))).1 =
        (c.re : Real) + -((F.q₂ : Real) - F.q₁) / 2
      linarith
    · change (TileCentroid (BandPackingSymmetryTileAction s (P 0 delta))).2 =
        (c.im : Real) + -(F.q : Real) / 2
      linarith
  rw [heq]
  ext <;> simp [GaussianRealPoint]

private theorem hFordCells :
    (by
      classical
      exact
        ∀ (F : FordFareyParameter), (FordTile F.q).cells.Nonempty ) := by
  classical
  intro F
  refine ⟨⟨0, 0⟩, ?_⟩
  simp [FordTile, FordCellDomain, F.q_pos]

private theorem hUnon :
    (by
      classical
      exact
        ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (r : Fin 3 → Bool → PartialOdometer), ∀ (x :
            GaussianInt), ∀ (F : FordFareyParameter), ∀ (s : BandPackingSymmetry), ∀ (delta : Bool),
        let c := BandPackingSymmetryVectorAction s x
        let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
        let hp := PartialOdometerAffineTranslate
          (BandPackingSymmetryPartialOdometerAction s (r 0 (!delta))) (-c) 0 0
        (TileOdometer (FordCircleCoordinate F.p F.q) U hp) → (∀ (k : PartialOdometer),
            (TileOdometer (FordCircleCoordinate F.p F.q) (FordTile F.q) k) → (((FordTile
            F.q).cells.Nonempty) → (U.cells.Nonempty))) ) := by
  classical
  intro P r x F s delta c U hp hplus' k hkO hFordCells
  obtain ⟨u₀, hu₀, _⟩ := BandPrototileTranslationNormalForm
    (FordCircleCoordinate F.p F.q) U (FordTile F.q)
    (TileOdometerBandPrototile _ _ _ hplus')
    (TileOdometerBandPrototile _ _ _ hkO)
  rw [hu₀]
  exact hFordCells.image _

private theorem hVnon :
    (by
      classical
      exact
        ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (r : Fin 3 → Bool → PartialOdometer), ∀ (x :
            GaussianInt), ∀ (F : FordFareyParameter), ∀ (s : BandPackingSymmetry), ∀ (delta : Bool),
        let c := BandPackingSymmetryVectorAction s x
        let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
        let hm := PartialOdometerAffineTranslate
          (BandPackingSymmetryPartialOdometerAction s (r 0 delta)) (-c) 0 0
        (TileOdometer (FordCircleCoordinate F.p F.q) V hm) → (∀ (k : PartialOdometer),
            (TileOdometer (FordCircleCoordinate F.p F.q) (FordTile F.q) k) → (((FordTile
            F.q).cells.Nonempty) → (V.cells.Nonempty))) ) := by
  classical
  intro P r x F s delta c V hm hminus' k hkO hFordCells
  obtain ⟨u₀, hu₀, _⟩ := BandPrototileTranslationNormalForm
    (FordCircleCoordinate F.p F.q) V (FordTile F.q)
    (TileOdometerBandPrototile _ _ _ hminus')
    (TileOdometerBandPrototile _ _ _ hkO)
  rw [hu₀]
  exact hFordCells.image _

private theorem huPlusEq :
    (by
      classical
      exact
        ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), ∀ (F : FordFareyParameter), ∀ (s :
            BandPackingSymmetry), ∀ (delta : Bool),
        let c := BandPackingSymmetryVectorAction s x
        let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
        ((F.q : Real) = (F.q₁ : Real) + F.q₂) → ((TileCentroid U = (((F.q₂ : Real) - F.q₁) / 2,
            (F.q : Real) / 2)) → ((TileCentroid (FordTile F.q) = ((↑F.q : ℝ) / (2 : ℝ), (↑F.q :
            ℝ) / (2 : ℝ))) → (∀ (uPlus : GaussianInt), (FootprintVertices U = FootprintVertices
            (TileTranslation (FordTile F.q) uPlus) ∧ BoundaryFootprintVertices U =
            BoundaryFootprintVertices (TileTranslation (FordTile F.q) uPlus) ∧
            BoundaryFootprintEdges U = BoundaryFootprintEdges (TileTranslation (FordTile F.q)
            uPlus) ∧ TileRealization U = TileRealization (TileTranslation (FordTile F.q) uPlus) ∧
            TileCentroid U = TileCentroid (TileTranslation (FordTile F.q) uPlus)) → (uPlus =
            ⟨-(F.q₁ : Int), 0⟩)))) ) := by
  classical
  intro P x F s delta c U hsumReal hUcent hFordCent uPlus hobsPlus
  have hh := hobsPlus.2.2.2.2
  rw [(TileTranslationFormulas (FordTile F.q) uPlus).2.2.2.2.1,
    hFordCent, hUcent] at hh
  apply Zsqrtd.ext
  · have h := congrArg Prod.fst hh
    apply Int.cast_injective (α := Real)
    dsimp at h ⊢
    push_cast at h ⊢
    linarith [F.sum_q]
  · have h := congrArg Prod.snd hh
    apply Int.cast_injective (α := Real)
    dsimp at h ⊢
    push_cast at h ⊢
    linarith

private theorem huMinusEq :
    (by
      classical
      exact
        ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), ∀ (F : FordFareyParameter), ∀ (s :
            BandPackingSymmetry), ∀ (delta : Bool),
        let c := BandPackingSymmetryVectorAction s x
        let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
        ((F.q : Real) = (F.q₁ : Real) + F.q₂) → ((TileCentroid V = (-((F.q₂ : Real) - F.q₁) / 2,
            -(F.q : Real) / 2)) → ((TileCentroid (FordTile F.q) = ((↑F.q : ℝ) / (2 : ℝ), (↑F.q :
            ℝ) / (2 : ℝ))) → (∀ (uMinus : GaussianInt), (FootprintVertices V = FootprintVertices
            (TileTranslation (FordTile F.q) uMinus) ∧ BoundaryFootprintVertices V =
            BoundaryFootprintVertices (TileTranslation (FordTile F.q) uMinus) ∧
            BoundaryFootprintEdges V = BoundaryFootprintEdges (TileTranslation (FordTile F.q)
            uMinus) ∧ TileRealization V = TileRealization (TileTranslation (FordTile F.q) uMinus)
            ∧ TileCentroid V = TileCentroid (TileTranslation (FordTile F.q) uMinus)) → (uMinus =
            ⟨-(F.q₂ : Int), -(F.q : Int)⟩)))) ) := by
  classical
  intro P x F s delta c V hsumReal hVcent hFordCent uMinus hobsMinus
  have hh := hobsMinus.2.2.2.2
  rw [(TileTranslationFormulas (FordTile F.q) uMinus).2.2.2.2.1,
    hFordCent, hVcent] at hh
  apply Zsqrtd.ext
  · have h := congrArg Prod.fst hh
    apply Int.cast_injective (α := Real)
    dsimp at h ⊢
    push_cast at h ⊢
    linarith [F.sum_q]
  · have h := congrArg Prod.snd hh
    apply Int.cast_injective (α := Real)
    dsimp at h ⊢
    push_cast at h ⊢
    linarith

private theorem hcellsPlus :
    (by
      classical
      exact
        ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), ∀ (F : FordFareyParameter), ∀ (s :
            BandPackingSymmetry), ∀ (delta : Bool),
        let c := BandPackingSymmetryVectorAction s x
        let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
        ∀ (uPlus : GaussianInt), (U.cells = (TileTranslation (FordTile F.q) uPlus).cells) →
            ((uPlus = ⟨-(F.q₁ : Int), 0⟩) → (U.cells = (TileTranslation (FordTile F.q) ⟨-(F.q₁ :
            Int), 0⟩).cells)) ) := by
  classical
  intro P x F s delta c U uPlus huPlus huPlusEq
  simpa [huPlusEq] using huPlus

private theorem hcellsMinus :
    (by
      classical
      exact
        ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (x : GaussianInt), ∀ (F : FordFareyParameter), ∀ (s :
            BandPackingSymmetry), ∀ (delta : Bool),
        let c := BandPackingSymmetryVectorAction s x
        let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
        ∀ (uMinus : GaussianInt), (V.cells = (TileTranslation (FordTile F.q) uMinus).cells) →
            ((uMinus = ⟨-(F.q₂ : Int), -(F.q : Int)⟩) → (V.cells = (TileTranslation (FordTile
            F.q) ⟨-(F.q₂ : Int), -(F.q : Int)⟩).cells)) ) := by
  classical
  intro P x F s delta c V uMinus huMinus huMinusEq
  simpa [huMinusEq] using huMinus

private theorem hcurvPos :
    (by
      classical
      exact
        ∀ (F : FordFareyParameter), 0 < (FordCircleCoordinate F.p F.q).1 ) := by
  classical
  intro F
  simp only [FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg, mul_self_pos, ne_eq,
      Int.natCast_eq_zero]
  exact Nat.ne_of_gt F.q_pos

private theorem hfootFord :
    (by
      classical
      exact
        ∀ (F : FordFareyParameter), ∀ (k : PartialOdometer), ((↑k.domain : Set GaussianInt) =
            FordVertexDomain F.q) → (((↑k.domain : Set GaussianInt) = FootprintVertices (FordTile
            F.q)) → (FootprintVertices (FordTile F.q) = FordVertexDomain F.q)) ) := by
  classical
  intro F k hkd hdomFord
  calc
    FootprintVertices (FordTile F.q) = k.domain := hdomFord.symm
    _ = FordVertexDomain F.q := hkd

private theorem hdomainPlus :
    (by
      classical
      exact
        ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (r : Fin 3 → Bool → PartialOdometer), ∀ (x :
            GaussianInt), ∀ (F : FordFareyParameter), ∀ (s : BandPackingSymmetry), ∀ (delta : Bool),
        let c := BandPackingSymmetryVectorAction s x
        let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
        let hp := PartialOdometerAffineTranslate
          (BandPackingSymmetryPartialOdometerAction s (r 0 (!delta))) (-c) 0 0
        ∀ (uPlus : GaussianInt), (FootprintVertices U = FootprintVertices (TileTranslation
            (FordTile F.q) uPlus) ∧ BoundaryFootprintVertices U = BoundaryFootprintVertices
            (TileTranslation (FordTile F.q) uPlus) ∧ BoundaryFootprintEdges U =
            BoundaryFootprintEdges (TileTranslation (FordTile F.q) uPlus) ∧ TileRealization U =
            TileRealization (TileTranslation (FordTile F.q) uPlus) ∧ TileCentroid U =
            TileCentroid (TileTranslation (FordTile F.q) uPlus)) → ((uPlus = ⟨-(F.q₁ : Int), 0⟩)
            → (((↑hp.domain : Set GaussianInt) = FootprintVertices U) → ((FootprintVertices
            (FordTile F.q) = FordVertexDomain F.q) → (((F.q : Int) = F.q₁ + F.q₂) → (∀ (z :
            GaussianInt), z ∈ hp.domain ↔ -(F.q₁ : Int) ≤ z.re ∧ z.re ≤ F.q₂ ∧ 0 ≤ z.im ∧ z.im ≤
            F.q))))) ) := by
  classical
  intro P r x F s delta c U hp uPlus hobsPlus huPlusEq hdomPlus hfootFord hsumInt z
  change z ∈ (hp.domain : Set GaussianInt) ↔ _
  rw [hdomPlus, hobsPlus.1,
    (TileTranslationFormulas (FordTile F.q) uPlus).2.2.2.2.2.1, hfootFord,
    huPlusEq]
  simp only [Set.mem_image, FordVertexDomain, Set.mem_ofPred_eq,
    GaussianTranslation]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Zsqrtd.re_add, Zsqrtd.im_add]
    omega
  · rintro ⟨hr1, hr2, hi1, hi2⟩
    refine ⟨z - ⟨-(F.q₁ : Int), 0⟩, ?_, ?_⟩
    · dsimp [FordVertexDomain]
      simp []
      omega
    · abel

private theorem hdomainMinus :
    (by
      classical
      exact
        ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (r : Fin 3 → Bool → PartialOdometer), ∀ (x :
            GaussianInt), ∀ (F : FordFareyParameter), ∀ (s : BandPackingSymmetry), ∀ (delta : Bool),
        let c := BandPackingSymmetryVectorAction s x
        let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
        let hm := PartialOdometerAffineTranslate
          (BandPackingSymmetryPartialOdometerAction s (r 0 delta)) (-c) 0 0
        ∀ (uMinus : GaussianInt), (FootprintVertices V = FootprintVertices (TileTranslation
            (FordTile F.q) uMinus) ∧ BoundaryFootprintVertices V = BoundaryFootprintVertices
            (TileTranslation (FordTile F.q) uMinus) ∧ BoundaryFootprintEdges V =
            BoundaryFootprintEdges (TileTranslation (FordTile F.q) uMinus) ∧ TileRealization V =
            TileRealization (TileTranslation (FordTile F.q) uMinus) ∧ TileCentroid V =
            TileCentroid (TileTranslation (FordTile F.q) uMinus)) → ((uMinus = ⟨-(F.q₂ : Int),
            -(F.q : Int)⟩) → (((↑hm.domain : Set GaussianInt) = FootprintVertices V) →
            ((FootprintVertices (FordTile F.q) = FordVertexDomain F.q) → (((F.q : Int) = F.q₁ +
            F.q₂) → (∀ (z : GaussianInt), z ∈ hm.domain ↔ -(F.q₂ : Int) ≤ z.re ∧ z.re ≤ F.q₁ ∧
            -(F.q : Int) ≤ z.im ∧ z.im ≤ 0))))) ) := by
  classical
  intro P r x F s delta c V hm uMinus hobsMinus huMinusEq hdomMinus hfootFord hsumInt z
  change z ∈ (hm.domain : Set GaussianInt) ↔ _
  rw [hdomMinus, hobsMinus.1,
    (TileTranslationFormulas (FordTile F.q) uMinus).2.2.2.2.2.1, hfootFord,
    huMinusEq]
  simp only [Set.mem_image, FordVertexDomain, Set.mem_ofPred_eq,
    GaussianTranslation]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Zsqrtd.re_add, Zsqrtd.im_add]
    omega
  · rintro ⟨hr1, hr2, hi1, hi2⟩
    refine ⟨z - ⟨-(F.q₂ : Int), -(F.q : Int)⟩, ?_, ?_⟩
    · dsimp [FordVertexDomain]
      simp []
      omega
    · abel

end LiteralFordPlacementGeometry

theorem P5472T1LiteralFordPlacement
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T)
    (h : PartialOdometer)
    (P : Fin 3 → Bool → ProtoTile)
    (r : Fin 3 → Bool → PartialOdometer)
    (Q S : Fin 3 → Bool → ProtoTile)
    (u v : Fin 3 → Bool → PartialOdometer)
    (g : IntegerLatticeFunction) (x : GaussianInt)
    (data : BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g)
    (hcenter : GaussianRealPoint x = TileCentroid T)
    (F : FordFareyParameter) (s : BandPackingSymmetry) (delta : Bool)
    (hrev : BandPackingSymmetryReversesOrientation s = false)
    (hword : ∃ z : GaussianInt, s = .shift z ∨ s = (BandPackingSymmetry.shift z).comp .negate)
    (hphase : BandPackingSymmetryScopedPhase s q delta)
    (hrootCircle : BandPackingSymmetryCircleAction s (q 1) = FordCircleCoordinate F.p F.q)
    (hW : BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
      (BandPackingSymmetryQuadrupleAction s q 2) = ⟨-(F.q₁ : Int), (F.q₂ : Int)⟩) :
    let c := BandPackingSymmetryVectorAction s x
    let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
    let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
    let hp := PartialOdometerAffineTranslate
      (BandPackingSymmetryPartialOdometerAction s (r 0 (!delta))) (-c) 0 0
    let hm := PartialOdometerAffineTranslate
      (BandPackingSymmetryPartialOdometerAction s (r 0 delta)) (-c) 0 0
    U.cells = (TileTranslation (FordTile F.q) ⟨-(F.q₁ : Int), 0⟩).cells ∧
    V.cells = (TileTranslation (FordTile F.q) ⟨-(F.q₂ : Int), -(F.q : Int)⟩).cells ∧
    TileOdometer (FordCircleCoordinate F.p F.q) U hp ∧
    TileOdometer (FordCircleCoordinate F.p F.q) V hm ∧
    (∀ z : GaussianInt, z ∈ hp.domain ↔
      -(F.q₁ : Int) ≤ z.re ∧ z.re ≤ F.q₂ ∧ 0 ≤ z.im ∧ z.im ≤ F.q) ∧
    (∀ z : GaussianInt, z ∈ hm.domain ↔
      -(F.q₂ : Int) ≤ z.re ∧ z.re ≤ F.q₁ ∧ -(F.q : Int) ≤ z.im ∧ z.im ≤ 0) := by
-- BODY
  let c := BandPackingSymmetryVectorAction s x
  let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
  let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
  let hp := PartialOdometerAffineTranslate
    (BandPackingSymmetryPartialOdometerAction s (r 0 (!delta))) (-c) 0 0
  let hm := PartialOdometerAffineTranslate
    (BandPackingSymmetryPartialOdometerAction s (r 0 delta)) (-c) 0 0
  have hplus' := LiteralFordPlacementGeometry.hplus' q cfg C0 T cert h P r Q S u v g x data F s
      delta hrootCircle
  have hminus' := LiteralFordPlacementGeometry.hminus' q cfg C0 T cert h P r Q S u v g x data F s
      delta hrootCircle
  have hocc (i : Fin 3) (b : Bool) := LiteralFordPlacementGeometry.hocc q cfg C0 T cert h P r Q S
      u v g data i b
  obtain ⟨d, e, P', hdphase, he, hPmap, hPocc, hPcover⟩ :=
    (BandPackingSymmetryCovariance s).2.2 q T P cfg.proper data.hPband
      hocc data.hPcells
  have hd : d = delta :=
    BandPackingSymmetryScopedPhaseUnique s q cfg.proper d delta hdphase hphase
  subst d
  have hePlus := LiteralFordPlacementGeometry.hePlus s delta hrev e he
  have heMinus := LiteralFordPlacementGeometry.heMinus s delta hrev e he
  have hPplusCent := LiteralFordPlacementGeometry.hPplusCent q T P s delta e P' hPmap hPocc hePlus
  have hPminusCent := LiteralFordPlacementGeometry.hPminusCent q T P s delta e P' hPmap hPocc
      heMinus
  have hcenter' := LiteralFordPlacementGeometry.hcenter' T x hcenter s hword
  have hsumReal : (F.q : Real) = (F.q₁ : Real) + F.q₂ := by exact_mod_cast F.sum_q
  have hDplus := LiteralFordPlacementGeometry.hDplus F hsumReal
  have hDminus := LiteralFordPlacementGeometry.hDminus F hsumReal
  have hUcent := LiteralFordPlacementGeometry.hUcent q T P x F s delta hW hPplusCent hcenter' hDplus
  have hVcent := LiteralFordPlacementGeometry.hVcent q T P x F s delta hW hPminusCent hcenter'
      hDminus
  obtain ⟨k, hkO, hkd, _⟩ := FordTileOdometerRestriction F
  have hFordCent := P4210T1FordSquareCentroid F.q F.q_pos
  have hFordCells := LiteralFordPlacementGeometry.hFordCells F
  have hUnon := LiteralFordPlacementGeometry.hUnon P r x F s delta hplus' k hkO hFordCells
  have hVnon := LiteralFordPlacementGeometry.hVnon P r x F s delta hminus' k hkO hFordCells
  obtain ⟨uPlus, huPlus, _⟩ := BandPrototileTranslationNormalForm
    (FordCircleCoordinate F.p F.q) U (FordTile F.q)
    (TileOdometerBandPrototile _ _ _ hplus')
    (TileOdometerBandPrototile _ _ _ hkO)
  obtain ⟨uMinus, huMinus, _⟩ := BandPrototileTranslationNormalForm
    (FordCircleCoordinate F.p F.q) V (FordTile F.q)
    (TileOdometerBandPrototile _ _ _ hminus')
    (TileOdometerBandPrototile _ _ _ hkO)
  have hobsPlus := ProtoTileObservableExtensionality U
    (TileTranslation (FordTile F.q) uPlus) huPlus (by
      intro hempty
      have hne := hUnon
      rw [hempty] at hne
      simp at hne)
  have hobsMinus := ProtoTileObservableExtensionality V
    (TileTranslation (FordTile F.q) uMinus) huMinus (by
      intro hempty
      have hne := hVnon
      rw [hempty] at hne
      simp at hne)
  have huPlusEq := LiteralFordPlacementGeometry.huPlusEq P x F s delta hsumReal hUcent hFordCent
      uPlus hobsPlus
  have huMinusEq := LiteralFordPlacementGeometry.huMinusEq P x F s delta hsumReal hVcent
      hFordCent uMinus hobsMinus
  have hcellsPlus := LiteralFordPlacementGeometry.hcellsPlus P x F s delta uPlus huPlus huPlusEq
  have hcellsMinus := LiteralFordPlacementGeometry.hcellsMinus P x F s delta uMinus huMinus
      huMinusEq
  have hcurvPos := LiteralFordPlacementGeometry.hcurvPos F
  have hdomPlus := PositiveCurvatureTileOdometerDomain
    (FordCircleCoordinate F.p F.q) U hp hcurvPos hplus'
  have hdomMinus := PositiveCurvatureTileOdometerDomain
    (FordCircleCoordinate F.p F.q) V hm hcurvPos hminus'
  have hdomFord := PositiveCurvatureTileOdometerDomain
    (FordCircleCoordinate F.p F.q) (FordTile F.q) k hcurvPos hkO
  have hfootFord := LiteralFordPlacementGeometry.hfootFord F k hkd hdomFord
  have hsumInt : (F.q : Int) = F.q₁ + F.q₂ := by exact_mod_cast F.sum_q
  have hdomainPlus (z : GaussianInt) := LiteralFordPlacementGeometry.hdomainPlus P r x F s delta
      uPlus hobsPlus huPlusEq hdomPlus hfootFord hsumInt z
  have hdomainMinus (z : GaussianInt) := LiteralFordPlacementGeometry.hdomainMinus P r x F s
      delta uMinus hobsMinus huMinusEq hdomMinus hfootFord hsumInt z
  exact ⟨hcellsPlus, hcellsMinus, hplus', hminus', hdomainPlus, hdomainMinus⟩

end ApollonianSuperharmonic

end
