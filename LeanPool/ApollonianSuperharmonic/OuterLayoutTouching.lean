/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.OuterTouchingAlternative
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: OuterLayoutTouching]

/-!
# OuterLayoutTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OuterTouchingProof

private theorem retarget :
    (by
      classical
      exact
        ∀ (K : CircleCoordinates), ∀ (X : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (Y
            : ProtoTile), BandPrototile K U → BandPrototile K V → TileCentroid U = TileCentroid V
            → TouchingTriple X U Y → TouchingTriple X V Y
    ) := by
  classical
  intro K X U V Y hU hV hUV h
  obtain ⟨he, ha⟩ := BandPrototileCentroidUnique K U V hU hV hUV
  have obs := ProtoTileObservableExtensionality U V he ha
  have left : TileTouching X U ↔ TileTouching X V := by
    by_cases hz : U.cells = ∅
    · simp only [TileTouching, he, obs.2.1, obs.2.2.1, ha hz]
    · have hz' : V.cells ≠ ∅ := by rwa [← he]
      simp only [TileTouching, hz', false_and, or_false, he,
        obs.2.1, obs.2.2.1]
  have right : TileTouching U Y ↔ TileTouching V Y := by
    by_cases hz : U.cells = ∅
    · simp only [TileTouching, he, obs.2.1, obs.2.2.1, ha hz]
    · have hz' : V.cells ≠ ∅ := by rwa [← he]
      simp only [TileTouching, hz', false_and, he,
        obs.2.1, obs.2.2.1]
  simpa only [TouchingTriple, left, right, obs.2.1] using h

private theorem row1 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)),
            BandPrototile (r (0 : Fin (4 : ℕ))) T₀ → BandPrototile (r i.succ) Tᵢ → TileCentroid
            Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s :
            ℕ)] (BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) →
            TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1
            (r i.succ) (r (0 : Fin (4 : ℕ)))))) Tᵢ) → (∀ (x : ℝ × ℝ), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile),
        let A := S 0 true
        let B := S 0 false
        let E := S 2 true
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let c := BandVectors.1 (q 2) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        (c = -a - b) → ((v = I * c + a) → ((BandVectors.1 (r 0) (r 3) = b) → ((BandVectors.1 (r
            3) (r 0) = -I * b) → ((BandPrototile (r 0) A) → ((BandPrototile (r 0) B) →
            ((BandPrototile (r 3) E) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt), TileCentroid
            (TileTranslation T z) = TileCentroid T + GaussianRealPoint z) → (((TileCentroid A).1
            - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) → (((TileCentroid A).2 - x.2 = (2
            : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex
            : GaussianInt → ℂ) a).re)) → (((TileCentroid B).1 - x.1 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) a).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im))) → (((TileCentroid B).2 - x.2 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re))) → (((TileCentroid E).1 - x.1 = (2 : ℝ)⁻¹ *
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid E).2 - x.2 = (2
            : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex
            : GaussianInt → ℂ) b).im - (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re))) → ((∀ (K : CircleCoordinates), ∀
            (X : ProtoTile), ∀ (X' : ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt),
            (BandPrototile K X) → ((BandPrototile K X') → ((TileCentroid X' - TileCentroid X =
            GaussianRealPoint z) → ((TouchingTriple X (TileTranslation X z) Y) → (TouchingTriple
            X X' Y))))) → (TouchingTriple A (TileTranslation B v) (TileTranslation E
            v)))))))))))))))))
    ) := by
  classical
  intro q r hT4r x S A B E I a b c v hc hv hr03 hr30 hA hB hE shift hAx hAy hBx hBy hEx hEy literal
  have h : TouchingTriple (TileTranslation B v) A (TileTranslation E v) := by
    refine literal (r 0) (TileTranslation B v) A (TileTranslation E v)
      ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 3) (r 0)))
      (BandPrototileTranslation _ _ _ hB) hA ?_
      (hT4r (TileTranslation B v) (TileTranslation E v) 2 2
        (BandPrototileTranslation _ _ _ hB)
        (BandPrototileTranslation _ _ _ hE) ?_)
    · apply Prod.ext <;>
        simp [shift, hv, hc, hr30, GaussianRealPoint, GaussianQuarterTurn, I,
          Function.iterate_succ_apply] <;>
        linarith only [hAx, hAy, hBx, hBy]
    · change TileCentroid (TileTranslation E v) - TileCentroid (TileTranslation B v) =
        (1 / 2 : Real) •
          (GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 3) (r 0))) +
            GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 0) (r 3))))
      apply Prod.ext <;>
        simp [shift, hv, hc, hr30, hr03, GaussianRealPoint, GaussianQuarterTurn, I,
          Function.iterate_succ_apply] <;>
        linarith only [hBx, hBy, hEx, hEy]
  exact ((TouchingTriplePermutations _ _ _).mp h).2.1

private theorem row2 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)),
            BandPrototile (r (0 : Fin (4 : ℕ))) T₀ → BandPrototile (r i.succ) Tᵢ → TileCentroid
            Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s :
            ℕ)] (BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) →
            TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1
            (r i.succ) (r (0 : Fin (4 : ℕ)))))) Tᵢ) → (∀ (x : ℝ × ℝ), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile),
        let A := S 0 true
        let B := S 0 false
        let F := S 2 false
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let c := BandVectors.1 (q 2) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        (c = -a - b) → ((v = I * c + a) → ((BandVectors.1 (r 0) (r 3) = b) → ((BandVectors.1 (r
            3) (r 0) = -I * b) → ((BandPrototile (r 0) A) → ((BandPrototile (r 0) B) →
            ((BandPrototile (r 3) F) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt), TileCentroid
            (TileTranslation T z) = TileCentroid T + GaussianRealPoint z) → (((TileCentroid A).1
            - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) → (((TileCentroid A).2 - x.2 = (2
            : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex
            : GaussianInt → ℂ) a).re)) → (((TileCentroid B).1 - x.1 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) a).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).im))) → (((TileCentroid B).2 - x.2 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re))) → (((TileCentroid F).1 - x.1 = -((2 : ℝ)⁻¹ *
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)))) → (((TileCentroid F).2 - x.2 =
            -((2 : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im - (-((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re - ((GaussianInt.toComplex : GaussianInt → ℂ) b).re)))) → ((∀
            (K : CircleCoordinates), ∀ (X : ProtoTile), ∀ (X' : ProtoTile), ∀ (Y : ProtoTile), ∀
            (z : GaussianInt), (BandPrototile K X) → ((BandPrototile K X') → ((TileCentroid X' -
            TileCentroid X = GaussianRealPoint z) → ((TouchingTriple X (TileTranslation X z) Y) →
            (TouchingTriple X X' Y))))) → (TouchingTriple A (TileTranslation B v) F))))))))))))))))
    ) := by
  classical
  intro q r hT4r x S A B F I a b c v hc hv hr03 hr30 hA hB hF shift hAx hAy hBx hBy hFx hFy literal
  refine literal (r 0) A (TileTranslation B v) F
    (BandVectors.1 (r 3) (r 0)) hA
    (BandPrototileTranslation _ _ _ hB) ?_ (hT4r A F 2 0 hA hF ?_)
  · apply Prod.ext <;>
      simp [shift, hv, hc, hr30, GaussianRealPoint, I] <;>
      linarith only [hAx, hAy, hBx, hBy]
  · change TileCentroid F - TileCentroid A = (1 / 2 : Real) •
      (GaussianRealPoint (BandVectors.1 (r 3) (r 0)) +
        GaussianRealPoint (BandVectors.1 (r 0) (r 3)))
    apply Prod.ext <;>
      simp [hr30, hr03, GaussianRealPoint, I] <;>
      linarith only [hAx, hAy, hFx, hFy]

private theorem row3 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)),
            BandPrototile (r (0 : Fin (4 : ℕ))) T₀ → BandPrototile (r i.succ) Tᵢ → TileCentroid
            Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s :
            ℕ)] (BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) →
            TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1
            (r i.succ) (r (0 : Fin (4 : ℕ)))))) Tᵢ) → (∀ (x : ℝ × ℝ), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile),
        let A := S 0 true
        let B := S 0 false
        let C := S 1 true
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let c := BandVectors.1 (q 2) (q 1)
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        (c = -a - b) → ((u = I * b + c) → ((v = I * c + a) → ((BandVectors.1 (r 2) (r 0) = c) →
            ((BandVectors.1 (r 0) (r 2) = I * c) → ((BandPrototile (r 0) A) → ((BandPrototile (r
            0) B) → ((BandPrototile (r 2) C) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt),
            TileCentroid (TileTranslation T z) = TileCentroid T + GaussianRealPoint z) →
            (((TileCentroid A).1 - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ)
            a).re + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) → (((TileCentroid A).2 -
            x.2 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).re)) → (((TileCentroid B).1 - x.1 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid B).2 - x.2 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).re))) → (((TileCentroid C).1 - x.1 = (2
            : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex
            : GaussianInt → ℂ) b).im)) → (((TileCentroid C).2 - x.2 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re)) → ((∀ (K : CircleCoordinates), ∀ (X : ProtoTile), ∀ (X' :
            ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt), (BandPrototile K X) →
            ((BandPrototile K X') → ((TileCentroid X' - TileCentroid X = GaussianRealPoint z) →
            ((TouchingTriple X (TileTranslation X z) Y) → (TouchingTriple X X' Y))))) →
            (TouchingTriple A (TileTranslation B (u + v)) (TileTranslation C (u +
            v)))))))))))))))))))
    ) := by
  classical
  intro q r hT4r x S A B C I a b c u v hc hu hv hr20 hr02 hA hB hC shift hAx hAy hBx hBy hCx hCy
      literal
  refine literal (r 0) A (TileTranslation B (u + v)) (TileTranslation C (u + v))
    (BandVectors.1 (r 2) (r 0)) hA
    (BandPrototileTranslation _ _ _ hB) ?_
    (hT4r A (TileTranslation C (u + v)) 1 0 hA
      (BandPrototileTranslation _ _ _ hC) ?_)
  · apply Prod.ext <;>
      simp [shift, hu, hv, hc, hr20, GaussianRealPoint, I] <;>
      linarith only [hAx, hAy, hBx, hBy]
  · change TileCentroid (TileTranslation C (u + v)) - TileCentroid A =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (r 2) (r 0)) +
        GaussianRealPoint (BandVectors.1 (r 0) (r 2)))
    apply Prod.ext <;>
      simp [shift, hu, hv, hc, hr20, hr02, GaussianRealPoint, I] <;>
      linarith only [hAx, hAy, hCx, hCy]

private theorem row4 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)),
            BandPrototile (r (0 : Fin (4 : ℕ))) T₀ → BandPrototile (r i.succ) Tᵢ → TileCentroid
            Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s :
            ℕ)] (BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) →
            TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1
            (r i.succ) (r (0 : Fin (4 : ℕ)))))) Tᵢ) → (∀ (x : ℝ × ℝ), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile),
        let A := S 0 true
        let B := S 0 false
        let D := S 1 false
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let c := BandVectors.1 (q 2) (q 1)
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        (c = -a - b) → ((u = I * b + c) → ((v = I * c + a) → ((BandVectors.1 (r 2) (r 0) = c) →
            ((BandVectors.1 (r 0) (r 2) = I * c) → ((BandPrototile (r 0) A) → ((BandPrototile (r
            0) B) → ((BandPrototile (r 2) D) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt),
            TileCentroid (TileTranslation T z) = TileCentroid T + GaussianRealPoint z) →
            (((TileCentroid A).1 - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ)
            a).re + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) → (((TileCentroid A).2 -
            x.2 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).re)) → (((TileCentroid B).1 - x.1 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid B).2 - x.2 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).re))) → (((TileCentroid D).1 - x.1 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im))) → (((TileCentroid D).2 - x.2 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re))) → ((∀ (K : CircleCoordinates), ∀
            (X : ProtoTile), ∀ (X' : ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt),
            (BandPrototile K X) → ((BandPrototile K X') → ((TileCentroid X' - TileCentroid X =
            GaussianRealPoint z) → ((TouchingTriple X (TileTranslation X z) Y) → (TouchingTriple
            X X' Y))))) → (TouchingTriple A (TileTranslation B (u + v)) D)))))))))))))))))
    ) := by
  classical
  intro q r hT4r x S A B D I a b c u v hc hu hv hr20 hr02 hA hB hD shift hAx hAy hBx hBy hDx hDy
      literal
  have h : TouchingTriple (TileTranslation B (u + v)) A D := by
    refine literal (r 0) (TileTranslation B (u + v)) A D
      ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 2) (r 0)))
      (BandPrototileTranslation _ _ _ hB) hA ?_
      (hT4r (TileTranslation B (u + v)) D 1 2
        (BandPrototileTranslation _ _ _ hB) hD ?_)
    · apply Prod.ext <;>
        simp [shift, hu, hv, hc, hr20, GaussianRealPoint, GaussianQuarterTurn, I,
          Function.iterate_succ_apply] <;>
        linarith only [hAx, hAy, hBx, hBy]
    · change TileCentroid D - TileCentroid (TileTranslation B (u + v)) =
        (1 / 2 : Real) •
          (GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 2) (r 0))) +
            GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 0) (r 2))))
      apply Prod.ext <;>
        simp [shift, hu, hv, hc, hr20, hr02, GaussianRealPoint, GaussianQuarterTurn, I,
          Function.iterate_succ_apply] <;>
        linarith only [hBx, hBy, hDx, hDy]
  exact ((TouchingTriplePermutations _ _ _).mp h).2.1

private theorem row5 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (Tⱼ : ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin
            (4 : ℕ)), BandPrototile (r (0 : Fin (4 : ℕ))) T₀ → BandPrototile (r i.succ) Tᵢ →
            BandPrototile (r (i + (1 : Fin (3 : ℕ))).succ) Tⱼ → TileCentroid Tᵢ - TileCentroid T₀
            = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (r
            i.succ) (r (0 : Fin (4 : ℕ))))) + GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)]
            (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) → TileCentroid Tⱼ - TileCentroid
            T₀ = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1
            (r (i + (1 : Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))))) - GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin
            (3 : ℕ))).succ)))) → TouchingTriple T₀ Tᵢ Tⱼ) → (∀ (x : ℝ × ℝ), ∀ (S : Fin (3 : ℕ) →
            Bool → ProtoTile),
        let A := S 0 true
        let C := S 1 true
        let E := S 2 true
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let c := BandVectors.1 (q 2) (q 1)
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        (c = -a - b) → ((u = I * b + c) → ((v = I * c + a) → ((BandVectors.1 (r 2) (r 0) = c) →
            ((BandVectors.1 (r 0) (r 2) = I * c) → ((BandVectors.1 (r 0) (r 3) = b) →
            ((BandVectors.1 (r 3) (r 0) = -I * b) → ((BandPrototile (r 0) A) → ((BandPrototile (r
            2) C) → ((BandPrototile (r 3) E) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt),
            TileCentroid (TileTranslation T z) = TileCentroid T + GaussianRealPoint z) →
            (((TileCentroid A).1 - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ)
            a).re + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)) → (((TileCentroid A).2 -
            x.2 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).re)) → (((TileCentroid C).1 - x.1 = (2
            : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex
            : GaussianInt → ℂ) b).im)) → (((TileCentroid C).2 - x.2 = (2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re)) → (((TileCentroid E).1 - x.1 = (2 : ℝ)⁻¹ *
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid E).2 - x.2 = (2
            : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex
            : GaussianInt → ℂ) b).im - (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re))) → (TouchingTriple A
            (TileTranslation C (u + v)) (TileTranslation E v)))))))))))))))))))
    ) := by
  classical
  intro q r hT5r x S A C E I a b c u v hc hu hv hr20 hr02 hr03 hr30 hA hC hE shift hAx hAy hCx
      hCy hEx hEy
  apply hT5r A (TileTranslation C (u + v)) (TileTranslation E v) 1 0 hA
    (BandPrototileTranslation _ _ _ hC) (BandPrototileTranslation _ _ _ hE)
  · change TileCentroid (TileTranslation C (u + v)) - TileCentroid A =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (r 2) (r 0)) +
        GaussianRealPoint (BandVectors.1 (r 0) (r 2)))
    apply Prod.ext <;>
      simp [shift, hu, hv, hc, hr20, hr02, GaussianRealPoint, I] <;>
      linarith only [hAx, hAy, hCx, hCy]
  · change TileCentroid (TileTranslation E v) - TileCentroid A =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (r 3) (r 0)) -
        GaussianRealPoint (BandVectors.1 (r 0) (r 3)))
    apply Prod.ext <;>
      simp [shift, hv, hc, hr30, hr03, GaussianRealPoint, I] <;>
      linarith only [hAx, hAy, hEx, hEy]

private theorem row6 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (Tⱼ : ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin
            (4 : ℕ)), BandPrototile (r (0 : Fin (4 : ℕ))) T₀ → BandPrototile (r i.succ) Tᵢ →
            BandPrototile (r (i + (1 : Fin (3 : ℕ))).succ) Tⱼ → TileCentroid Tᵢ - TileCentroid T₀
            = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (r
            i.succ) (r (0 : Fin (4 : ℕ))))) + GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)]
            (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) → TileCentroid Tⱼ - TileCentroid
            T₀ = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1
            (r (i + (1 : Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))))) - GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin
            (3 : ℕ))).succ)))) → TouchingTriple T₀ Tᵢ Tⱼ) → (∀ (x : ℝ × ℝ), ∀ (S : Fin (3 : ℕ) →
            Bool → ProtoTile),
        let B := S 0 false
        let D := S 1 false
        let F := S 2 false
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let c := BandVectors.1 (q 2) (q 1)
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        (c = -a - b) → ((u = I * b + c) → ((v = I * c + a) → ((BandVectors.1 (r 2) (r 0) = c) →
            ((BandVectors.1 (r 0) (r 2) = I * c) → ((BandVectors.1 (r 0) (r 3) = b) →
            ((BandVectors.1 (r 3) (r 0) = -I * b) → ((BandPrototile (r 0) B) → ((BandPrototile (r
            2) D) → ((BandPrototile (r 3) F) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt),
            TileCentroid (TileTranslation T z) = TileCentroid T + GaussianRealPoint z) →
            (((TileCentroid B).1 - x.1 = -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt →
            ℂ) a).re + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid B).2
            - x.2 = -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).re))) → (((TileCentroid D).1 - x.1 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im))) → (((TileCentroid D).2 - x.2 =
            -((2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re))) → (((TileCentroid F).1 - x.1 =
            -((2 : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re - (((GaussianInt.toComplex :
            GaussianInt → ℂ) b).im + ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)))) →
            (((TileCentroid F).2 - x.2 = -((2 : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt →
            ℂ) a).im - ((GaussianInt.toComplex : GaussianInt → ℂ) b).im -
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re)))) → (TouchingTriple B (TileTranslation D (-u - v))
            (TileTranslation F (-v))))))))))))))))))))
    ) := by
  classical
  intro q r hT5r x S B D F I a b c u v hc hu hv hr20 hr02 hr03 hr30 hB hD hF shift hBx hBy hDx
      hDy hFx hFy
  apply hT5r B (TileTranslation D (-u - v)) (TileTranslation F (-v)) 1 2 hB
    (BandPrototileTranslation _ _ _ hD) (BandPrototileTranslation _ _ _ hF)
  · change TileCentroid (TileTranslation D (-u - v)) - TileCentroid B =
      (1 / 2 : Real) •
        (GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 2) (r 0))) +
          GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 0) (r 2))))
    apply Prod.ext <;>
      simp [shift, hu, hv, hc, hr20, hr02, GaussianRealPoint, GaussianQuarterTurn, I,
        Function.iterate_succ_apply] <;>
      linarith only [hBx, hBy, hDx, hDy]
  · change TileCentroid (TileTranslation F (-v)) - TileCentroid B =
      (1 / 2 : Real) •
        (GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 3) (r 0))) -
          GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (r 0) (r 3))))
    apply Prod.ext <;>
      simp [shift, hv, hc, hr30, hr03, GaussianRealPoint, GaussianQuarterTurn, I,
        Function.iterate_succ_apply] <;>
      linarith only [hBx, hBy, hFx, hFy]

private theorem row7 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)),
            BandPrototile (t (0 : Fin (4 : ℕ))) T₀ → BandPrototile (t i.succ) Tᵢ → TileCentroid
            Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s :
            ℕ)] (BandVectors.1 (t i.succ) (t (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t (0 : Fin (4 : ℕ))) (t i.succ)))) →
            TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1
            (t i.succ) (t (0 : Fin (4 : ℕ)))))) Tᵢ) → (∀ (x : ℝ × ℝ), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile),
        let C := S 1 true
        let D := S 1 false
        let E := S 2 true
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let c := BandVectors.1 (q 2) (q 1)
        let u := BandVectors.1 (q 0) (q 1)
        (c = -a - b) → ((u = I * b + c) → ((BandVectors.1 (t 1) (t 0) = a) → ((BandVectors.1 (t
            0) (t 1) = I * a) → ((BandPrototile (t 0) C) → ((BandPrototile (t 0) D) →
            ((BandPrototile (t 1) E) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt), TileCentroid
            (TileTranslation T z) = TileCentroid T + GaussianRealPoint z) → (((TileCentroid C).1
            - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im)) → (((TileCentroid C).2 - x.2 = (2
            : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex
            : GaussianInt → ℂ) b).re)) → (((TileCentroid D).1 - x.1 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).im))) → (((TileCentroid D).2 - x.2 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re))) → (((TileCentroid E).1 - x.1 = (2 : ℝ)⁻¹ *
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im))) → (((TileCentroid E).2 - x.2 = (2
            : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im - ((GaussianInt.toComplex
            : GaussianInt → ℂ) b).im - (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).re))) → ((∀ (K : CircleCoordinates), ∀
            (X : ProtoTile), ∀ (X' : ProtoTile), ∀ (Y : ProtoTile), ∀ (z : GaussianInt),
            (BandPrototile K X) → ((BandPrototile K X') → ((TileCentroid X' - TileCentroid X =
            GaussianRealPoint z) → ((TouchingTriple X (TileTranslation X z) Y) → (TouchingTriple
            X X' Y))))) → (TouchingTriple C (TileTranslation D (-u)) (TileTranslation E
            (-u))))))))))))))))))
    ) := by
  classical
  intro q t hT4t x S C D E I a b c u hc hu ht10 ht01 hCt hDt hEt shift hCx hCy hDx hDy hEx hEy
      literal
  refine literal (t 0) C (TileTranslation D (-u)) (TileTranslation E (-u))
    (BandVectors.1 (t 1) (t 0)) hCt
    (BandPrototileTranslation _ _ _ hDt) ?_
    (hT4t C (TileTranslation E (-u)) 0 0 hCt
      (BandPrototileTranslation _ _ _ hEt) ?_)
  · apply Prod.ext <;>
      simp [shift, hu, hc, ht10, GaussianRealPoint, I] <;>
      linarith only [hCx, hCy, hDx, hDy]
  · change TileCentroid (TileTranslation E (-u)) - TileCentroid C =
      (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (t 1) (t 0)) +
        GaussianRealPoint (BandVectors.1 (t 0) (t 1)))
    apply Prod.ext <;>
      simp [shift, hu, hc, ht10, ht01, GaussianRealPoint, I] <;>
      linarith only [hCx, hCy, hEx, hEy]

private theorem row8 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), (∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)),
            BandPrototile (t (0 : Fin (4 : ℕ))) T₀ → BandPrototile (t i.succ) Tᵢ → TileCentroid
            Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s :
            ℕ)] (BandVectors.1 (t i.succ) (t (0 : Fin (4 : ℕ))))) + GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (t (0 : Fin (4 : ℕ))) (t i.succ)))) →
            TouchingTriple T₀ (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1
            (t i.succ) (t (0 : Fin (4 : ℕ)))))) Tᵢ) → (∀ (x : ℝ × ℝ), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile),
        let C := S 1 true
        let D := S 1 false
        let F := S 2 false
        let I : GaussianInt := ⟨0, 1⟩
        let a := BandVectors.1 (q 3) (q 2)
        let b := BandVectors.1 (q 1) (q 3)
        let c := BandVectors.1 (q 2) (q 1)
        let u := BandVectors.1 (q 0) (q 1)
        (c = -a - b) → ((u = I * b + c) → ((BandVectors.1 (t 1) (t 0) = a) → ((BandVectors.1 (t
            0) (t 1) = I * a) → ((BandPrototile (t 0) C) → ((BandPrototile (t 0) D) →
            ((BandPrototile (t 1) F) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt), TileCentroid
            (TileTranslation T z) = TileCentroid T + GaussianRealPoint z) → (((TileCentroid C).1
            - x.1 = (2 : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im)) → (((TileCentroid C).2 - x.2 = (2
            : ℝ)⁻¹ * (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex
            : GaussianInt → ℂ) b).re)) → (((TileCentroid D).1 - x.1 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).im))) → (((TileCentroid D).2 - x.2 = -((2 : ℝ)⁻¹ *
            (((GaussianInt.toComplex : GaussianInt → ℂ) b).im - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re))) → (((TileCentroid F).1 - x.1 = -((2 : ℝ)⁻¹ *
            (-((GaussianInt.toComplex : GaussianInt → ℂ) a).re - ((GaussianInt.toComplex :
            GaussianInt → ℂ) b).re - (((GaussianInt.toComplex : GaussianInt → ℂ) b).im +
            ((GaussianInt.toComplex : GaussianInt → ℂ) a).im)))) → (((TileCentroid F).2 - x.2 =
            -((2 : ℝ)⁻¹ * (-((GaussianInt.toComplex : GaussianInt → ℂ) a).im -
            ((GaussianInt.toComplex : GaussianInt → ℂ) b).im - (-((GaussianInt.toComplex :
            GaussianInt → ℂ) a).re - ((GaussianInt.toComplex : GaussianInt → ℂ) b).re)))) → ((∀
            (K : CircleCoordinates), ∀ (X : ProtoTile), ∀ (X' : ProtoTile), ∀ (Y : ProtoTile), ∀
            (z : GaussianInt), (BandPrototile K X) → ((BandPrototile K X') → ((TileCentroid X' -
            TileCentroid X = GaussianRealPoint z) → ((TouchingTriple X (TileTranslation X z) Y) →
            (TouchingTriple X X' Y))))) → (TouchingTriple C (TileTranslation D (-u))
            F))))))))))))))))
    ) := by
  classical
  intro q t hT4t x S C D F I a b c u hc hu ht10 ht01 hCt hDt hFt shift hCx hCy hDx hDy hFx hFy
      literal
  have h : TouchingTriple (TileTranslation D (-u)) C F := by
    refine literal (t 0) (TileTranslation D (-u)) C F
      ((GaussianQuarterTurn^[2]) (BandVectors.1 (t 1) (t 0)))
      (BandPrototileTranslation _ _ _ hDt) hCt ?_
      (hT4t (TileTranslation D (-u)) F 0 2
        (BandPrototileTranslation _ _ _ hDt) hFt ?_)
    · apply Prod.ext <;>
        simp [shift, hu, hc, ht10, GaussianRealPoint, GaussianQuarterTurn, I,
          Function.iterate_succ_apply] <;>
        linarith only [hCx, hCy, hDx, hDy]
    · change TileCentroid F - TileCentroid (TileTranslation D (-u)) =
        (1 / 2 : Real) •
          (GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (t 1) (t 0))) +
            GaussianRealPoint ((GaussianQuarterTurn^[2]) (BandVectors.1 (t 0) (t 1))))
      apply Prod.ext <;>
        simp [shift, hu, hc, ht10, ht01, GaussianRealPoint, GaussianQuarterTurn, I,
          Function.iterate_succ_apply] <;>
        linarith only [hDx, hDy, hFx, hFy]
  exact ((TouchingTriplePermutations _ _ _).mp h).2.1

end OuterTouchingProof

theorem OuterLayoutTouching :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (r : Fin 4 → CircleCoordinates), ∀ (t : Fin 4 →
        CircleCoordinates), (ProperBandQuadruple q) → ((ProperBandQuadruple r) →
        ((ProperBandQuadruple t) → ((r 0 = q 1) → ((r 2 = q 2) → ((r 3 = q 3) → ((t 0 = q 2) →
        ((t 1 = q 3) → (((r 0).1 < (q 0).1) → (((t 0).1 < (q 0).1) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ
        : ProtoTile), ∀ (i : Fin 3), ∀ (s : Fin 4), BandPrototile (r 0) T₀ → BandPrototile (r
        i.succ) Tᵢ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (r i.succ) (r 0))) +
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (r 0) (r i.succ)))) →
      TouchingTriple T₀
        (TileTranslation T₀
          ((GaussianQuarterTurn^[s.val])
            (BandVectors.1 (r i.succ) (r 0)))) Tᵢ) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀
                (Tⱼ : ProtoTile), ∀ (i : Fin 3), ∀ (s : Fin 4), BandPrototile (r 0) T₀ →
                BandPrototile (r i.succ) Tᵢ →
      BandPrototile (r ((i + 1).succ)) Tⱼ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (r i.succ) (r 0))) +
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (r 0) (r i.succ)))) →
      TileCentroid Tⱼ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (r ((i + 1).succ)) (r 0))) -
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (r 0) (r ((i + 1).succ))))) →
      TouchingTriple T₀ Tᵢ Tⱼ) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (i : Fin 3), ∀ (s :
          Fin 4), BandPrototile (t 0) T₀ → BandPrototile (t i.succ) Tᵢ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (t i.succ) (t 0))) +
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (t 0) (t i.succ)))) →
      TouchingTriple T₀
        (TileTranslation T₀
          ((GaussianQuarterTurn^[s.val])
            (BandVectors.1 (t i.succ) (t 0)))) Tᵢ) → ((∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀
                (Tⱼ : ProtoTile), ∀ (i : Fin 3), ∀ (s : Fin 4), BandPrototile (t 0) T₀ →
                BandPrototile (t i.succ) Tᵢ →
      BandPrototile (t ((i + 1).succ)) Tⱼ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (t i.succ) (t 0))) +
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (t 0) (t i.succ)))) →
      TileCentroid Tⱼ - TileCentroid T₀ =
        (1 / 2 : Real) •
          (GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (t ((i + 1).succ)) (t 0))) -
            GaussianRealPoint
              ((GaussianQuarterTurn^[s.val])
                (BandVectors.1 (t 0) (t ((i + 1).succ))))) →
      TouchingTriple T₀ Tᵢ Tⱼ) → (∀ (x : Real × Real), ∀ (S : Fin 3 → Bool → ProtoTile), (∀ i, ∀
          s, BandPrototile (q i.succ) (S i s)) → ((∀ i, ∀ s, TileCentroid (S i s) - x =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint
                (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
              (-((GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).2),
                (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).1)))) → (let A := S 0 true
    let B := S 0 false
    let C := S 1 true
    let D := S 1 false
    let E := S 2 true
    let F := S 2 false
    let u := BandVectors.1 (q 0) (q 1)
    let v := BandVectors.1 (q 0) (q 2)
    OuterTouchingAlternative A (TileTranslation B v) (TileTranslation E v) ∧
      OuterTouchingAlternative A (TileTranslation B v) F ∧
      OuterTouchingAlternative A (TileTranslation B (u + v))
        (TileTranslation C (u + v)) ∧
      OuterTouchingAlternative A (TileTranslation B (u + v)) D ∧
      OuterTouchingAlternative A (TileTranslation C (u + v))
        (TileTranslation E v) ∧
      OuterTouchingAlternative B (TileTranslation D (-u - v))
        (TileTranslation F (-v)) ∧
      OuterTouchingAlternative C (TileTranslation D (-u))
        (TileTranslation E (-u)) ∧
      OuterTouchingAlternative C (TileTranslation D (-u)) F)))))))))))))))) := by
  intro q r t hq hr ht hr0 hr2 hr3 ht0 ht1 hrlt htlt hT4r hT5r hT4t hT5t x S hS hcent
-- BODY
  let A := S 0 true
  let B := S 0 false
  let C := S 1 true
  let D := S 1 false
  let E := S 2 true
  let F := S 2 false
  let I : GaussianInt := ⟨0, 1⟩
  let a := BandVectors.1 (q 3) (q 2)
  let b := BandVectors.1 (q 1) (q 3)
  let c := BandVectors.1 (q 2) (q 1)
  let u := BandVectors.1 (q 0) (q 1)
  let v := BandVectors.1 (q 0) (q 2)
  change OuterTouchingAlternative A (TileTranslation B v) (TileTranslation E v) ∧
    OuterTouchingAlternative A (TileTranslation B v) F ∧
    OuterTouchingAlternative A (TileTranslation B (u + v)) (TileTranslation C (u + v)) ∧
    OuterTouchingAlternative A (TileTranslation B (u + v)) D ∧
    OuterTouchingAlternative A (TileTranslation C (u + v)) (TileTranslation E v) ∧
    OuterTouchingAlternative B (TileTranslation D (-u - v)) (TileTranslation F (-v)) ∧
    OuterTouchingAlternative C (TileTranslation D (-u)) (TileTranslation E (-u)) ∧
    OuterTouchingAlternative C (TileTranslation D (-u)) F
  obtain ⟨hsum, _, hin1, _, flipq⟩ := VectorRecursionLaws q hq.1
  have hin2 : BandVectors.1 (q 2) (q 0) = c - I * a := by
    simpa [a, c, I] using
      (VectorRecursionLaws _ (SemiProperQuadruple.rotate hq.1)).2.2.1
  have hc : c = -a - b := by
    change a + b + c = 0 at hsum
    calc
      c = (a + b + c) - a - b := by ring
      _ = -a - b := by rw [hsum]; ring
  have hu : u = I * b + c := by
    change BandVectors.1 (q 1) (q 0) = b - I * c at hin1
    have h := (flipq hq 0).1
    change u = I * BandVectors.1 (q 1) (q 0) at h
    rw [h, hin1]
    ext <;> simp [I]; ring
  have hv : v = I * c + a := by
    have h := (flipq hq 1).1
    change v = I * BandVectors.1 (q 2) (q 0) at h
    rw [h, hin2]
    ext <;> simp [I]; ring
  have flipr := (VectorRecursionLaws r hr.1).2.2.2.2 hr
  have flipt := (VectorRecursionLaws t ht.1).2.2.2.2 ht
  have hr20 : BandVectors.1 (r 2) (r 0) = c := by rw [hr2, hr0]
  have hr02 : BandVectors.1 (r 0) (r 2) = I * c := by
    have h := (flipr 1).1
    change BandVectors.1 (r 0) (r 2) = I * BandVectors.1 (r 2) (r 0) at h
    simpa [hr20] using h
  have hr03 : BandVectors.1 (r 0) (r 3) = b := by rw [hr0, hr3]
  have hr30 : BandVectors.1 (r 3) (r 0) = -I * b := by
    have h := (flipr 2).1
    change BandVectors.1 (r 0) (r 3) = I * BandVectors.1 (r 3) (r 0) at h
    rw [hr03] at h
    calc
      _ = -I * (I * BandVectors.1 (r 3) (r 0)) := by
        ext <;> simp [I]
      _ = -I * b := by rw [← h]
  have ht10 : BandVectors.1 (t 1) (t 0) = a := by rw [ht1, ht0]
  have ht01 : BandVectors.1 (t 0) (t 1) = I * a := by
    have h := (flipt 0).1
    change BandVectors.1 (t 0) (t 1) = I * BandVectors.1 (t 1) (t 0) at h
    simpa [ht10] using h
  have hA : BandPrototile (r 0) A := by rw [hr0]; exact hS 0 true
  have hB : BandPrototile (r 0) B := by rw [hr0]; exact hS 0 false
  have hC : BandPrototile (r 2) C := by rw [hr2]; exact hS 1 true
  have hD : BandPrototile (r 2) D := by rw [hr2]; exact hS 1 false
  have hE : BandPrototile (r 3) E := by rw [hr3]; exact hS 2 true
  have hF : BandPrototile (r 3) F := by rw [hr3]; exact hS 2 false
  have hCt : BandPrototile (t 0) C := by rw [ht0]; exact hS 1 true
  have hDt : BandPrototile (t 0) D := by rw [ht0]; exact hS 1 false
  have hEt : BandPrototile (t 1) E := by rw [ht1]; exact hS 2 true
  have hFt : BandPrototile (t 1) F := by rw [ht1]; exact hS 2 false
  have shift (T : ProtoTile) (z : GaussianInt) :
      TileCentroid (TileTranslation T z) = TileCentroid T + GaussianRealPoint z :=
    (TileTranslationFormulas T z).2.2.2.2.1
  have retarget (K : CircleCoordinates) (X U V Y : ProtoTile)
      (hU : BandPrototile K U) (hV : BandPrototile K V)
      (hUV : TileCentroid U = TileCentroid V)
      (h : TouchingTriple X U Y) : TouchingTriple X V Y := OuterTouchingProof.retarget K X U V Y
          hU hV hUV h
  have centerA := hcent 0 true
  have centerB := hcent 0 false
  have centerC := hcent 1 true
  have centerD := hcent 1 false
  have centerE := hcent 2 true
  have centerF := hcent 2 false
  change TileCentroid A - x = (1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint a - (-(GaussianRealPoint a).2, (GaussianRealPoint a).1))) at centerA
  change TileCentroid B - x = (-1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint a - (-(GaussianRealPoint a).2, (GaussianRealPoint a).1))) at centerB
  change TileCentroid C - x = (1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint b - (-(GaussianRealPoint b).2, (GaussianRealPoint b).1))) at centerC
  change TileCentroid D - x = (-1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint b - (-(GaussianRealPoint b).2, (GaussianRealPoint b).1))) at centerD
  change TileCentroid E - x = (1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint c - (-(GaussianRealPoint c).2, (GaussianRealPoint c).1))) at centerE
  change TileCentroid F - x = (-1 : Real) • ((1 / 2 : Real) •
    (GaussianRealPoint c - (-(GaussianRealPoint c).2, (GaussianRealPoint c).1))) at centerF
  rw [hc] at centerE centerF
  have hAx := congrArg Prod.fst centerA
  have hAy := congrArg Prod.snd centerA
  have hBx := congrArg Prod.fst centerB
  have hBy := congrArg Prod.snd centerB
  have hCx := congrArg Prod.fst centerC
  have hCy := congrArg Prod.snd centerC
  have hDx := congrArg Prod.fst centerD
  have hDy := congrArg Prod.snd centerD
  have hEx := congrArg Prod.fst centerE
  have hEy := congrArg Prod.snd centerE
  have hFx := congrArg Prod.fst centerF
  have hFy := congrArg Prod.snd centerF
  simp? [GaussianRealPoint] at hAx hAy hBx hBy hCx hCy hDx hDy hEx hEy hFx hFy
  have literal (K : CircleCoordinates) (X X' Y : ProtoTile) (z : GaussianInt)
      (hX : BandPrototile K X) (hX' : BandPrototile K X')
      (hoff : TileCentroid X' - TileCentroid X = GaussianRealPoint z)
      (h : TouchingTriple X (TileTranslation X z) Y) : TouchingTriple X X' Y := by
    apply retarget K X (TileTranslation X z) X' Y
      (BandPrototileTranslation K X z hX) hX' _ h
    rw [shift, ← hoff]
    abel
  -- The T4 rows identify the literal second child by its centroid.
  have row1 : TouchingTriple A (TileTranslation B v) (TileTranslation E v) :=
      OuterTouchingProof.row1 q r hT4r x S hc hv hr03 hr30 hA hB hE shift hAx hAy hBx hBy hEx hEy
      literal
  have row2 : TouchingTriple A (TileTranslation B v) F := OuterTouchingProof.row2 q r hT4r x S hc
      hv hr03 hr30 hA hB hF shift hAx hAy hBx hBy hFx hFy literal
  have row3 : TouchingTriple A (TileTranslation B (u + v))
      (TileTranslation C (u + v)) := OuterTouchingProof.row3 q r hT4r x S hc hu hv hr20 hr02 hA
          hB hC shift hAx hAy hBx hBy hCx hCy literal
  have row4 : TouchingTriple A (TileTranslation B (u + v)) D := OuterTouchingProof.row4 q r hT4r
      x S hc hu hv hr20 hr02 hA hB hD shift hAx hAy hBx hBy hDx hDy literal
  have row5 : TouchingTriple A (TileTranslation C (u + v)) (TileTranslation E v) :=
      OuterTouchingProof.row5 q r hT5r x S hc hu hv hr20 hr02 hr03 hr30 hA hC hE shift hAx hAy
      hCx hCy hEx hEy
  have row6 : TouchingTriple B (TileTranslation D (-u - v))
      (TileTranslation F (-v)) := OuterTouchingProof.row6 q r hT5r x S hc hu hv hr20 hr02 hr03
          hr30 hB hD hF shift hBx hBy hDx hDy hFx hFy
  have row7 : TouchingTriple C (TileTranslation D (-u)) (TileTranslation E (-u)) :=
      OuterTouchingProof.row7 q t hT4t x S hc hu ht10 ht01 hCt hDt hEt shift hCx hCy hDx hDy hEx
      hEy literal
  have row8 : TouchingTriple C (TileTranslation D (-u)) F := OuterTouchingProof.row8 q t hT4t x S
      hc hu ht10 ht01 hCt hDt hFt shift hCx hCy hDx hDy hFx hFy literal
  exact ⟨Or.inl row1, Or.inl row2, Or.inl row3, Or.inl row4,
    Or.inl row5, Or.inl row6, Or.inl row7, Or.inl row8⟩

end ApollonianSuperharmonic

end
