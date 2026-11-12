/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProjectiveVectorCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryReversesOrientation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhase
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriplePackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.FordOrientedChildParentRightEndpoint
public import LeanPool.ApollonianSuperharmonic.FordRegimeConverse
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: BandOrientedChildParentRightEndpoint]

/-!
# BandOrientedChildParentRightEndpoint

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OrientedRightEndpointGeometry

private theorem hq :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), (ProperBandQuadruple r) → (∀ (a : Fin (3 : ℕ)), ∀ (g0
            : BandPackingSymmetry), ∀ (P : FordFareyParameter), ((r (a + (2 : Fin (3 :
            ℕ))).succ).1 = (0 : ℤ)) → ((BandPackingSymmetryQuadrupleAction g0 ![r (0 : Fin (4 :
            ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ, r (a + (2 : Fin (3 : ℕ))).succ] =
            FordRecursiveQuadruple P) → (
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ProperBandQuadruple q))) ) := by
  classical
  intro r hproper a g0 P hzero hford q
  fin_cases a
  · convert hproper using 1; funext x; fin_cases x <;> rfl
  · have rotated := SemiProperQuadruple.rotate hproper.1
    have properRotated : ProperBandQuadruple ![r 0, r 2, r 3, r 1] := by
      refine ⟨rotated, ?_⟩
      intro j
      fin_cases j
      · simpa using hproper.2 (1 : Fin 3)
      · simpa using hproper.2 (2 : Fin 3)
      · simpa using hproper.2 (0 : Fin 3)
    simpa [q] using properRotated
  · have rotated := SemiProperQuadruple.rotate
      (SemiProperQuadruple.rotate hproper.1)
    have properRotated : ProperBandQuadruple ![r 0, r 3, r 1, r 2] := by
      refine ⟨rotated, ?_⟩
      intro j
      fin_cases j
      · simpa using hproper.2 (2 : Fin 3)
      · simpa using hproper.2 (0 : Fin 3)
      · simpa using hproper.2 (1 : Fin 3)
    simpa [q] using properRotated

private theorem hzeroAction :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (a : Fin (3 : ℕ)), ∀ (g0 : BandPackingSymmetry), ∀
            (P : FordFareyParameter), (BandPackingSymmetryQuadrupleAction g0 ![r (0 : Fin (4 :
            ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ, r (a + (2 : Fin (3 : ℕ))).succ] =
            FordRecursiveQuadruple P) → (
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g : BandPackingSymmetry), (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
            BandPackingSymmetryQuadrupleAction g p = BandPackingSymmetryQuadrupleAction g0 p) →
            (BandPackingSymmetryQuadrupleAction g q = FordRecursiveQuadruple P)) ) := by
  classical
  intro r a g0 P hford q g hquadg
  rw [hquadg, hford]

private theorem hUford :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (U : ProtoTile), ∀ (a : Fin (3 : ℕ)), ∀ (P :
            FordFareyParameter),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g : BandPackingSymmetry), (BandPrototile (BandPackingSymmetryCircleAction g (r 0))
            (BandPackingSymmetryTileAction g U)) → ((BandPackingSymmetryQuadrupleAction g q =
            FordRecursiveQuadruple P) → (BandPrototile ((FordRecursiveQuadruple P) 0)
            (BandPackingSymmetryTileAction g U))) ) := by
  classical
  intro r U a P q g hU' hzeroAction
  have he := congrFun hzeroAction 0
  simpa [q, BandPackingSymmetryQuadrupleAction] using he ▸ hU'

private theorem hWford :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (Z : ProtoTile), (BandPrototile (r i.succ) W) → ((BandPrototile (r
            (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ) Z) →
            (((0 : ℤ) < (r i.succ).1) → ((TileCentroid W - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (r
            i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) →
            ((TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (r (0 : Fin (4 :
            ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) - BandVectors.1 (r (i - (1 : Fin (3 :
            ℕ))).succ) (r (0 : Fin (4 : ℕ))) else BandVectors.1 (r (i + (1 : Fin (3 : ℕ))).succ)
            (r (0 : Fin (4 : ℕ))) - BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin (3 :
            ℕ))).succ))) → ((0 ≤ (r ((if Even s.val then i - 1 else i + 1).succ)).1) → (((0 : ℤ)
            = (r (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 :
            ℕ))).succ).1) → (∀ (a : Fin (3 : ℕ)), ∀ (g0 : BandPackingSymmetry), ∀ (P :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation g0 = false) → (((r (a +
            (2 : Fin (3 : ℕ))).succ).1 = (0 : ℤ)) → ((BandPackingSymmetryQuadrupleAction g0 ![r
            (0 : Fin (4 : ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ, r (a + (2 : Fin (3 :
            ℕ))).succ] = FordRecursiveQuadruple P) → (
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        (ProperBandQuadruple q) → (∀ (negative : Bool), (BandPackingSymmetryScopedPhase g0 q
            negative) → ((∀ (r : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 :
            Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3
            : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g0 r negative)
            → ((∀ (t : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple t → t (0 : Fin (4 :
            ℕ)) = q (2 : Fin (4 : ℕ)) → t (1 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) →
            BandPackingSymmetryScopedPhase g0 t negative) → (∀ (g : BandPackingSymmetry),
            (BandPackingSymmetryReversesOrientation g = BandPackingSymmetryReversesOrientation
            g0) → ((BandPackingSymmetryScopedPhase g q false) → ((∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple r → r (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))
            → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3 : Fin (4 : ℕ)) = q (3 : Fin (4 :
            ℕ)) → BandPackingSymmetryScopedPhase g r false) → ((∀ (t : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple t → t (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))
            → t (1 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g t
            false) → ((BandPrototile (BandPackingSymmetryCircleAction g (r i.succ))
            (BandPackingSymmetryTileAction g W)) → (
        let k : Fin 3 := i - a
        (BandPackingSymmetryQuadrupleAction g q = FordRecursiveQuadruple P) → (BandPrototile
            ((FordRecursiveQuadruple P) k.succ) (BandPackingSymmetryTileAction g
            W))))))))))))))))))))) ) := by
  classical
  intro r i s U W Z hW hZ hWpos hWcent hZcent nonnegative zero a g0 P horient hzero hford q hq
      negative hphase hphase1 hphase2 g horientg hfalse hfalse1 hfalse2 hW' k hzeroAction
  have he := congrFun hzeroAction k.succ
  have source :
      BandPackingSymmetryQuadrupleAction g q k.succ =
        BandPackingSymmetryCircleAction g (r i.succ) := by
    fin_cases a <;> fin_cases i <;>
      simp [k, q, BandPackingSymmetryQuadrupleAction, horientg, horient]
  rw [source] at he
  exact he ▸ hW'

private theorem phaseForward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (Z : ProtoTile), (BandPrototile (r i.succ) W) → ((BandPrototile (r
            (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ) Z) →
            (((0 : ℤ) < (r i.succ).1) → ((TileCentroid W - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (r
            i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) →
            ((TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (r (0 : Fin (4 :
            ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) - BandVectors.1 (r (i - (1 : Fin (3 :
            ℕ))).succ) (r (0 : Fin (4 : ℕ))) else BandVectors.1 (r (i + (1 : Fin (3 : ℕ))).succ)
            (r (0 : Fin (4 : ℕ))) - BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin (3 :
            ℕ))).succ))) → ((0 ≤ (r ((if Even s.val then i - 1 else i + 1).succ)).1) → (((0 : ℤ)
            = (r (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 :
            ℕ))).succ).1) → (∀ (a : Fin (3 : ℕ)), ∀ (g0 : BandPackingSymmetry), ∀ (P :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation g0 = false) → (((r (a +
            (2 : Fin (3 : ℕ))).succ).1 = (0 : ℤ)) → ((BandPackingSymmetryQuadrupleAction g0 ![r
            (0 : Fin (4 : ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ, r (a + (2 : Fin (3 :
            ℕ))).succ] = FordRecursiveQuadruple P) → (
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        (ProperBandQuadruple q) → (∀ (negative : Bool), (BandPackingSymmetryScopedPhase g0 q
            negative) → ((∀ (r : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 :
            Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3
            : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g0 r negative)
            → ((∀ (t : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple t → t (0 : Fin (4 :
            ℕ)) = q (2 : Fin (4 : ℕ)) → t (1 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) →
            BandPackingSymmetryScopedPhase g0 t negative) → (∀ (g : BandPackingSymmetry),
            (BandPackingSymmetryReversesOrientation g = BandPackingSymmetryReversesOrientation
            g0) → ((BandPackingSymmetryScopedPhase g q false) → ((∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple r → r (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))
            → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3 : Fin (4 : ℕ)) = q (3 : Fin (4 :
            ℕ)) → BandPackingSymmetryScopedPhase g r false) → ((∀ (t : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple t → t (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))
            → t (1 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g t
            false) → ((BandPrototile (BandPackingSymmetryCircleAction g (r i.succ))
            (BandPackingSymmetryTileAction g W)) → (
        let k : Fin 3 := i - a
        (BandPackingSymmetryQuadrupleAction g q = FordRecursiveQuadruple P) → ((BandPrototile
            ((FordRecursiveQuadruple P) k.succ) (BandPackingSymmetryTileAction g W)) →
            (BandVectors.1 ((FordRecursiveQuadruple P) k.succ) ((FordRecursiveQuadruple P) 0) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r i.succ) (r
            0))))))))))))))))))))))) ) := by
  classical
  intro r i s U W Z hW hZ hWpos hWcent hZcent nonnegative zero a g0 P horient hzero hford q hq
      negative hphase hphase1 hphase2 g horientg hfalse hfalse1 hfalse2 hW' k hzeroAction hWford
  have phase := (show BandPackingSymmetryScopedPhase g q false from hfalse)
  simp only [BandPackingSymmetryScopedPhase] at phase
  rw [hzeroAction] at phase
  fin_cases a <;> fin_cases i <;>
    simpa [BandPackingSymmetryScopedPhase, horientg, horient, hzeroAction, q, k]
      using (phase k).1

private theorem phaseBackward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (Z : ProtoTile), (BandPrototile (r i.succ) W) → ((BandPrototile (r
            (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ) Z) →
            (((0 : ℤ) < (r i.succ).1) → ((TileCentroid W - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (r
            i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) →
            ((TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (r (0 : Fin (4 :
            ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) - BandVectors.1 (r (i - (1 : Fin (3 :
            ℕ))).succ) (r (0 : Fin (4 : ℕ))) else BandVectors.1 (r (i + (1 : Fin (3 : ℕ))).succ)
            (r (0 : Fin (4 : ℕ))) - BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin (3 :
            ℕ))).succ))) → ((0 ≤ (r ((if Even s.val then i - 1 else i + 1).succ)).1) → (((0 : ℤ)
            = (r (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 :
            ℕ))).succ).1) → (∀ (a : Fin (3 : ℕ)), ∀ (g0 : BandPackingSymmetry), ∀ (P :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation g0 = false) → (((r (a +
            (2 : Fin (3 : ℕ))).succ).1 = (0 : ℤ)) → ((BandPackingSymmetryQuadrupleAction g0 ![r
            (0 : Fin (4 : ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ, r (a + (2 : Fin (3 :
            ℕ))).succ] = FordRecursiveQuadruple P) → (
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        (ProperBandQuadruple q) → (∀ (negative : Bool), (BandPackingSymmetryScopedPhase g0 q
            negative) → ((∀ (r : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 :
            Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3
            : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g0 r negative)
            → ((∀ (t : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple t → t (0 : Fin (4 :
            ℕ)) = q (2 : Fin (4 : ℕ)) → t (1 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) →
            BandPackingSymmetryScopedPhase g0 t negative) → (∀ (g : BandPackingSymmetry),
            (BandPackingSymmetryReversesOrientation g = BandPackingSymmetryReversesOrientation
            g0) → ((BandPackingSymmetryScopedPhase g q false) → ((∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple r → r (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))
            → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3 : Fin (4 : ℕ)) = q (3 : Fin (4 :
            ℕ)) → BandPackingSymmetryScopedPhase g r false) → ((∀ (t : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple t → t (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))
            → t (1 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g t
            false) → ((BandPrototile (BandPackingSymmetryCircleAction g (r i.succ))
            (BandPackingSymmetryTileAction g W)) → (
        let k : Fin 3 := i - a
        (BandPackingSymmetryQuadrupleAction g q = FordRecursiveQuadruple P) → ((BandPrototile
            ((FordRecursiveQuadruple P) k.succ) (BandPackingSymmetryTileAction g W)) →
            ((BandVectors.1 ((FordRecursiveQuadruple P) k.succ) ((FordRecursiveQuadruple P) 0) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r i.succ) (r 0))) → (BandVectors.1
            ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) k.succ) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r 0) (r
            i.succ)))))))))))))))))))))))) ) := by
  classical
  intro r i s U W Z hW hZ hWpos hWcent hZcent nonnegative zero a g0 P horient hzero hford q hq
      negative hphase hphase1 hphase2 g horientg hfalse hfalse1 hfalse2 hW' k hzeroAction hWford
      phaseForward
  have phase := (show BandPackingSymmetryScopedPhase g q false from hfalse)
  simp only [BandPackingSymmetryScopedPhase] at phase
  rw [hzeroAction] at phase
  fin_cases a <;> fin_cases i <;>
    simpa [BandPackingSymmetryScopedPhase, horientg, horient, hzeroAction, q, k]
      using (phase k).2.1

private theorem centroidAction :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), (TileCentroid W - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (r i.succ) (r (0 :
            Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) → (∀ (g0 :
            BandPackingSymmetry), (∃ (w : GaussianInt), g0 = BandPackingSymmetry.shift w ∨ g0 =
            (BandPackingSymmetry.shift w).comp BandPackingSymmetry.negate) → (∀ (g :
            BandPackingSymmetry), (g = g0 ∨ g = (BandPackingSymmetry.negate.comp
            BandPackingSymmetry.negate).comp g0) → (TileCentroid (BandPackingSymmetryTileAction g
            W) - TileCentroid (BandPackingSymmetryTileAction g U) = (1 / 2 : Real) •
            GaussianRealPoint (BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val
            * (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))))))) ) := by
  classical
  intro r i s U W hWcent g0 hword g hglift
  rcases hglift with lift | lift
  · rw [lift]
    rcases hword with ⟨w, word | word⟩
    · rw [word]
      simpa [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction] using hWcent
    · rw [word]
      change TileCentroid (TileQuarterTurn W) -
        TileCentroid (TileQuarterTurn U) = _
      rw [(TileQuarterTurnFormulas W).2.2.2.2.1,
        (TileQuarterTurnFormulas U).2.2.2.2.1]
      have first := congrArg Prod.fst hWcent
      have second := congrArg Prod.snd hWcent
      simp [BandPackingSymmetryVectorAction, GaussianRealPoint,
        GaussianQuarterTurn] at first second ⊢
      constructor <;> linarith
  · rw [lift]
    rcases hword with ⟨w, word | word⟩
    · rw [word]
      change TileCentroid (TileQuarterTurn (TileQuarterTurn W)) -
        TileCentroid (TileQuarterTurn (TileQuarterTurn U)) = _
      rw [(TileQuarterTurnFormulas (TileQuarterTurn W)).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn U)).2.2.2.2.1,
        (TileQuarterTurnFormulas W).2.2.2.2.1,
        (TileQuarterTurnFormulas U).2.2.2.2.1]
      have first := congrArg Prod.fst hWcent
      have second := congrArg Prod.snd hWcent
      simp [BandPackingSymmetryVectorAction, GaussianRealPoint,
        GaussianQuarterTurn] at first second ⊢
      constructor <;> linarith
    · rw [word]
      change TileCentroid (TileQuarterTurn (TileQuarterTurn
          (TileQuarterTurn W))) -
        TileCentroid (TileQuarterTurn (TileQuarterTurn
          (TileQuarterTurn U))) = _
      rw [(TileQuarterTurnFormulas (TileQuarterTurn
          (TileQuarterTurn W))).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn
          (TileQuarterTurn U))).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn W)).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn U)).2.2.2.2.1,
        (TileQuarterTurnFormulas W).2.2.2.2.1,
        (TileQuarterTurnFormulas U).2.2.2.2.1]
      have first := congrArg Prod.fst hWcent
      have second := congrArg Prod.snd hWcent
      simp [BandPackingSymmetryVectorAction, GaussianRealPoint,
        GaussianQuarterTurn] at first second ⊢
      constructor <;> linarith

private theorem actionAdd :
    (by
      classical
      exact
        ∀ (g0 : BandPackingSymmetry), (∃ (w : GaussianInt), g0 = BandPackingSymmetry.shift w ∨ g0
            = (BandPackingSymmetry.shift w).comp BandPackingSymmetry.negate) → (∀ (g :
            BandPackingSymmetry), (g = g0 ∨ g = (BandPackingSymmetry.negate.comp
            BandPackingSymmetry.negate).comp g0) → (∀ (x : GaussianInt), ∀ (y : GaussianInt),
            BandPackingSymmetryVectorAction g (x + y) = BandPackingSymmetryVectorAction g x +
            BandPackingSymmetryVectorAction g y)) ) := by
  classical
  intro g0 hword g hglift x y
  rcases hglift with lift | lift
  · rw [lift]
    rcases hword with ⟨w, word | word⟩ <;> rw [word]
    · simp [BandPackingSymmetryVectorAction]
    · simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn,
        add_comm]
  · rw [lift]
    rcases hword with ⟨w, word | word⟩ <;> rw [word]
    · simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn,
        add_comm]
    · simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
      simp [add_comm]

private theorem actionCommute :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (Z : ProtoTile), (BandPrototile (r (if Even (↑s : ℕ) then i - (1 :
            Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ) Z) → ((TileCentroid W - TileCentroid U
            = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) *
            (BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ)))
            (r i.succ)))) → ((TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1
            (r (0 : Fin (4 : ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) - BandVectors.1 (r (i - (1 :
            Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))) else BandVectors.1 (r (i + (1 : Fin (3 :
            ℕ))).succ) (r (0 : Fin (4 : ℕ))) - BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i + (1 :
            Fin (3 : ℕ))).succ))) → ((0 ≤ (r ((if Even s.val then i - 1 else i + 1).succ)).1) →
            (((0 : ℤ) = (r (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 :
            ℕ))).succ).1) → (∀ (g0 : BandPackingSymmetry), (∃ (w : GaussianInt), g0 =
            BandPackingSymmetry.shift w ∨ g0 = (BandPackingSymmetry.shift w).comp
            BandPackingSymmetry.negate) → (∀ (g : BandPackingSymmetry), (g = g0 ∨ g =
            (BandPackingSymmetry.negate.comp BandPackingSymmetry.negate).comp g0) →
            ((TileCentroid (BandPackingSymmetryTileAction g W) - TileCentroid
            (BandPackingSymmetryTileAction g U) = (1 / 2 : Real) • GaussianRealPoint
            (BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1
            (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))))) → (∀ (x : GaussianInt),
            BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * x) = (⟨0, 1⟩ :
            GaussianInt) ^ s.val * BandPackingSymmetryVectorAction g x)))))))) ) := by
  classical
  intro r i s U W Z hZ hWcent hZcent nonnegative zero g0 hword g hglift centroidAction x
  rcases hglift with lift | lift
  · rw [lift]
    rcases hword with ⟨w, word | word⟩ <;> rw [word]
    · simp [BandPackingSymmetryVectorAction]
    · fin_cases s <;>
        apply Zsqrtd.ext <;>
          simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn] <;>
          ring
  · rw [lift]
    rcases hword with ⟨w, word | word⟩ <;> rw [word]
    · fin_cases s <;>
        apply Zsqrtd.ext <;>
          simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn] <;>
          ring
    · fin_cases s <;>
        apply Zsqrtd.ext <;>
          simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn] <;>
          ring

private theorem vectorIdentity :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin (3 : ℕ)), ∀
            (P : FordFareyParameter), ∀ (g : BandPackingSymmetry),
        let k : Fin 3 := i - a
        (BandVectors.1 ((FordRecursiveQuadruple P) k.succ) ((FordRecursiveQuadruple P) 0) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r i.succ) (r 0))) → ((BandVectors.1
            ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) k.succ) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r 0) (r i.succ))) → ((∀ (x :
            GaussianInt), ∀ (y : GaussianInt), BandPackingSymmetryVectorAction g (x + y) =
            BandPackingSymmetryVectorAction g x + BandPackingSymmetryVectorAction g y) → ((∀ (x :
            GaussianInt), BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * x)
            = (⟨0, 1⟩ : GaussianInt) ^ s.val * BandPackingSymmetryVectorAction g x) →
            (BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1
            (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))) = (⟨0, 1⟩ : GaussianInt) ^ s.val
            * (BandVectors.1 ((FordRecursiveQuadruple P) k.succ) ((FordRecursiveQuadruple P) 0) +
            BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) k.succ))))))
            ) := by
  classical
  intro r i s a P g k phaseForward phaseBackward actionAdd actionCommute
  rw [actionCommute, actionAdd, phaseForward, phaseBackward]

private theorem transformedCentroid :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (a : Fin (3 : ℕ)), ∀ (P : FordFareyParameter), ∀ (g :
            BandPackingSymmetry),
        let k : Fin 3 := i - a
        (TileCentroid (BandPackingSymmetryTileAction g W) - TileCentroid
            (BandPackingSymmetryTileAction g U) = (1 / 2 : Real) • GaussianRealPoint
            (BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1
            (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))))) →
            ((BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1
            (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))) = (⟨0, 1⟩ : GaussianInt) ^ s.val
            * (BandVectors.1 ((FordRecursiveQuadruple P) k.succ) ((FordRecursiveQuadruple P) 0) +
            BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) k.succ))) →
            (TileCentroid (BandPackingSymmetryTileAction g W) - TileCentroid
            (BandPackingSymmetryTileAction g U) = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ :
            GaussianInt) ^ s.val * (BandVectors.1 ((FordRecursiveQuadruple P) k.succ)
            ((FordRecursiveQuadruple P) 0) + BandVectors.1 ((FordRecursiveQuadruple P) 0)
            ((FordRecursiveQuadruple P) k.succ))))) ) := by
  classical
  intro r i s U W a P g k centroidAction vectorIdentity
  rw [centroidAction, vectorIdentity]

private theorem hUposFord :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ((0 : ℤ) < (r (0 : Fin (4 : ℕ))).1) → (∀ (a : Fin (3 :
            ℕ)), ∀ (g0 : BandPackingSymmetry), ∀ (P : FordFareyParameter),
            (BandPackingSymmetryReversesOrientation g0 = false) → (
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g : BandPackingSymmetry), (BandPackingSymmetryReversesOrientation g =
            BandPackingSymmetryReversesOrientation g0) → (((∀ (C : CircleCoordinates),
            (BandPackingSymmetryCircleAction g C).1 = C.1) ∧ (∀ (C : CircleCoordinates), ∀ (T :
            ProtoTile), BandPrototile C T ↔ BandPrototile (BandPackingSymmetryCircleAction g C)
            (BandPackingSymmetryTileAction g T)) ∧ ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T
            : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ProperBandQuadruple q →
            BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence q T i s (S i s)) → (∀ (x : LatticeCell), x ∈ T.cells ↔ ∃ (i :
            Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase g q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction g (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g q)
            (BandPackingSymmetryTileAction g T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction g T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S' i
            s).cells) → ((BandPackingSymmetryQuadrupleAction g q = FordRecursiveQuadruple P) → (0
            < ((FordRecursiveQuadruple P) 0).1))))) ) := by
  classical
  intro r hUpos a g0 P horient q g horientg tileCovariance hzeroAction
  have he := congrArg (fun x => (x 0).1) hzeroAction
  have he' : ((FordRecursiveQuadruple P) 0).1 = (r 0).1 := by
    calc
      ((FordRecursiveQuadruple P) 0).1 =
          (BandPackingSymmetryQuadrupleAction g q 0).1 := he.symm
      _ = (BandPackingSymmetryCircleAction g (r 0)).1 := by
        simp [q, BandPackingSymmetryQuadrupleAction, horientg, horient]
      _ = (r 0).1 := tileCovariance.1 _
  rw [he']
  exact hUpos

private theorem hWposFord :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (Z : ProtoTile), (BandPrototile (r i.succ) W) → ((BandPrototile (r
            (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ) Z) →
            (((0 : ℤ) < (r i.succ).1) → ((TileCentroid W - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (r
            i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) →
            ((TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (r (0 : Fin (4 :
            ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) - BandVectors.1 (r (i - (1 : Fin (3 :
            ℕ))).succ) (r (0 : Fin (4 : ℕ))) else BandVectors.1 (r (i + (1 : Fin (3 : ℕ))).succ)
            (r (0 : Fin (4 : ℕ))) - BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin (3 :
            ℕ))).succ))) → ((0 ≤ (r ((if Even s.val then i - 1 else i + 1).succ)).1) → (((0 : ℤ)
            = (r (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 :
            ℕ))).succ).1) → (∀ (a : Fin (3 : ℕ)), ∀ (g0 : BandPackingSymmetry), ∀ (P :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation g0 = false) → (((r (a +
            (2 : Fin (3 : ℕ))).succ).1 = (0 : ℤ)) → ((BandPackingSymmetryQuadrupleAction g0 ![r
            (0 : Fin (4 : ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ, r (a + (2 : Fin (3 :
            ℕ))).succ] = FordRecursiveQuadruple P) → (
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        (ProperBandQuadruple q) → (∀ (negative : Bool), (BandPackingSymmetryScopedPhase g0 q
            negative) → ((∀ (r : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 :
            Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3
            : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g0 r negative)
            → ((∀ (t : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple t → t (0 : Fin (4 :
            ℕ)) = q (2 : Fin (4 : ℕ)) → t (1 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) →
            BandPackingSymmetryScopedPhase g0 t negative) → (∀ (g : BandPackingSymmetry),
            (BandPackingSymmetryReversesOrientation g = BandPackingSymmetryReversesOrientation
            g0) → ((BandPackingSymmetryScopedPhase g q false) → ((∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple r → r (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))
            → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3 : Fin (4 : ℕ)) = q (3 : Fin (4 :
            ℕ)) → BandPackingSymmetryScopedPhase g r false) → ((∀ (t : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple t → t (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))
            → t (1 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g t
            false) → (((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction g C).1 = C.1)
            ∧ (∀ (C : CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction g C) (BandPackingSymmetryTileAction g T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase g q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction g (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g q)
            (BandPackingSymmetryTileAction g T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction g T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S' i
            s).cells) → ((BandPrototile (BandPackingSymmetryCircleAction g (r i.succ))
            (BandPackingSymmetryTileAction g W)) → (
        let k : Fin 3 := i - a
        (BandPackingSymmetryQuadrupleAction g q = FordRecursiveQuadruple P) → ((BandPrototile
            ((FordRecursiveQuadruple P) k.succ) (BandPackingSymmetryTileAction g W)) →
            ((BandVectors.1 ((FordRecursiveQuadruple P) k.succ) ((FordRecursiveQuadruple P) 0) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r i.succ) (r 0))) → ((BandVectors.1
            ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) k.succ) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r 0) (r i.succ))) → ((TileCentroid
            (BandPackingSymmetryTileAction g W) - TileCentroid (BandPackingSymmetryTileAction g
            U) = (1 / 2 : Real) • GaussianRealPoint (BandPackingSymmetryVectorAction g ((⟨0, 1⟩ :
            GaussianInt) ^ s.val * (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r
            i.succ))))) → ((BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))) = (⟨0, 1⟩ :
            GaussianInt) ^ s.val * (BandVectors.1 ((FordRecursiveQuadruple P) k.succ)
            ((FordRecursiveQuadruple P) 0) + BandVectors.1 ((FordRecursiveQuadruple P) 0)
            ((FordRecursiveQuadruple P) k.succ))) → ((TileCentroid (BandPackingSymmetryTileAction
            g W) - TileCentroid (BandPackingSymmetryTileAction g U) = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1
            ((FordRecursiveQuadruple P) k.succ) ((FordRecursiveQuadruple P) 0) + BandVectors.1
            ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) k.succ)))) → (0 <
            ((FordRecursiveQuadruple P) k.succ).1))))))))))))))))))))))))))) ) := by
  classical
  intro r i s U W Z hW hZ hWpos hWcent hZcent nonnegative zero a g0 P horient hzero hford q hq
      negative hphase hphase1 hphase2 g horientg hfalse hfalse1 hfalse2 tileCovariance hW' k
      hzeroAction hWford phaseForward phaseBackward centroidAction vectorIdentity
      transformedCentroid
  have he := congrArg (fun x => (x k.succ).1) hzeroAction
  have source :
      BandPackingSymmetryQuadrupleAction g q k.succ =
        BandPackingSymmetryCircleAction g (r i.succ) := by
    fin_cases a <;> fin_cases i <;>
      simp [k, q, BandPackingSymmetryQuadrupleAction, horientg, horient]
  have he' : ((FordRecursiveQuadruple P) k.succ).1 =
      (r i.succ).1 := by
    calc
      ((FordRecursiveQuadruple P) k.succ).1 =
          (BandPackingSymmetryQuadrupleAction g q k.succ).1 :=
        (congrArg (fun x => (x k.succ).1) hzeroAction).symm
      _ = (BandPackingSymmetryCircleAction g (r i.succ)).1 :=
        congrArg Prod.fst source
      _ = (r i.succ).1 := tileCovariance.1 _
  rw [he']
  exact hWpos

private theorem middleVector :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin (3 : ℕ)), ∀
            (P : FordFareyParameter), ∀ (g : BandPackingSymmetry),
        let k : Fin 3 := i - a
        (BandVectors.1 ((FordRecursiveQuadruple P) k.succ) ((FordRecursiveQuadruple P) 0) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r i.succ) (r 0))) → ((BandVectors.1
            ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P) k.succ) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (r 0) (r i.succ))) → ((∀ (x :
            GaussianInt), BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * x)
            = (⟨0, 1⟩ : GaussianInt) ^ s.val * BandPackingSymmetryVectorAction g x) →
            (BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * (if Even s.val
            then BandVectors.1 (r 0) (r i.succ) else BandVectors.1 (r i.succ) (r 0))) = (⟨0, 1⟩ :
            GaussianInt) ^ s.val * (if Even s.val then BandVectors.1 ((FordRecursiveQuadruple P)
            0) ((FordRecursiveQuadruple P) k.succ) else BandVectors.1 ((FordRecursiveQuadruple P)
            k.succ) ((FordRecursiveQuadruple P) 0))))) ) := by
  classical
  intro r i s a P g k phaseForward phaseBackward actionCommute
  by_cases parity : Even s.val
  · simp? [parity]
    rw [actionCommute, phaseBackward]
  · simp? [parity]
    rw [actionCommute, phaseForward]

private theorem transformedTriple :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (g : BandPackingSymmetry), ∀ [Nonempty
            (ExactTileInterfaceTriple (BandPackingSymmetryTileAction g U)
            (BandPackingSymmetryTileAction g (TileTranslation U ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (r (0 : Fin (4 : ℕ)))
            (r i.succ) else BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))))))
            (BandPackingSymmetryTileAction g W))], Nonempty (ExactTileInterfaceTriple
            (BandPackingSymmetryTileAction g U) (BandPackingSymmetryTileAction g (TileTranslation
            U ((⟨0, 1⟩ : GaussianInt) ^ s.val * (if Even s.val then BandVectors.1 (r 0) (r
            i.succ) else BandVectors.1 (r i.succ) (r 0))))) (BandPackingSymmetryTileAction g W))
            ) := by
  classical
  intro r i s U W g fordResult
  exact fordResult

end OrientedRightEndpointGeometry

theorem BandOrientedChildParentRightEndpoint
    (r : Fin 4 → CircleCoordinates) (hproper : ProperBandQuadruple r)
    (i : Fin 3) (s : Fin 4) (U W Z : ProtoTile)
    (hU : BandPrototile (r 0) U)
    (hW : BandPrototile (r i.succ) W)
    (hZ : BandPrototile
      (r ((if Even s.val then i - 1 else i + 1).succ)) Z)
    (hUpos : 0 < (r 0).1) (hWpos : 0 < (r i.succ).1)
    (hWcent : TileCentroid W - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (r i.succ) (r 0) +
            BandVectors.1 (r 0) (r i.succ))))
    (hZcent : TileCentroid Z - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then
            BandVectors.1 (r 0) (r ((i - 1).succ)) -
              BandVectors.1 (r ((i - 1).succ)) (r 0)
          else
            BandVectors.1 (r ((i + 1).succ)) (r 0) -
              BandVectors.1 (r 0) (r ((i + 1).succ))))) :
    let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (r 0) (r i.succ)
        else BandVectors.1 (r i.succ) (r 0))
    Nonempty (ExactTileInterfaceTriple U (TileTranslation U uR) W) := by
-- BODY
  dsimp
  have curvature := ProperBandCurvatureStructure r hproper
  have nonnegative : 0 ≤ (r ((if Even s.val then i - 1 else i + 1).succ)).1 := by
    exact curvature.2.1 (if Even s.val then i - 1 else i + 1)
  rcases lt_or_eq_of_le nonnegative with positive | zero
  · have result := BandOrientedChildParentEndpoints r hproper i s U W Z hU hW hZ
      hUpos hWpos positive hWcent hZcent
    exact ⟨result.choose⟩
  · obtain ⟨a, g0, P, hP, horient, hword, hzero, hford⟩ :=
      FordRegimeConverse r hproper
        ⟨(if Even s.val then i - 1 else i + 1).succ, zero.symm⟩
    let q : Fin 4 → CircleCoordinates :=
      ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
    have hq : ProperBandQuadruple q := OrientedRightEndpointGeometry.hq r hproper a g0 P hzero hford
    have hprojective := BandPackingSymmetryProjectiveVectorCovariance g0 q hq
    dsimp at hprojective
    rcases hprojective with ⟨negative, hphase, hphase1, hphase2, hcircle,
      horient', hquad, hvec, g, hglift, hcircle', horientg, hquadg, hfalse,
      hfalse1, hfalse2⟩
    have tileCovariance := BandPackingSymmetryCovariance g
    have hU' : BandPrototile
        (BandPackingSymmetryCircleAction g (r 0))
        (BandPackingSymmetryTileAction g U) :=
      (tileCovariance.2.1 _ _).mp hU
    have hW' : BandPrototile
        (BandPackingSymmetryCircleAction g (r i.succ))
        (BandPackingSymmetryTileAction g W) :=
      (tileCovariance.2.1 _ _).mp hW
    let k : Fin 3 := i - a
    have hzeroAction : BandPackingSymmetryQuadrupleAction g q =
        FordRecursiveQuadruple P := OrientedRightEndpointGeometry.hzeroAction r a g0 P hford g
            hquadg
    have hUford : BandPrototile
        ((FordRecursiveQuadruple P) 0)
        (BandPackingSymmetryTileAction g U) := OrientedRightEndpointGeometry.hUford r U a P g hU'
            hzeroAction
    have hWford : BandPrototile
        ((FordRecursiveQuadruple P) k.succ)
        (BandPackingSymmetryTileAction g W) := OrientedRightEndpointGeometry.hWford r i s U W Z
            hW hZ hWpos hWcent hZcent nonnegative zero a g0 P horient hzero hford hq negative
            hphase hphase1 hphase2 g horientg hfalse hfalse1 hfalse2 hW' hzeroAction
    have phaseForward :
        BandVectors.1 ((FordRecursiveQuadruple P) k.succ)
            ((FordRecursiveQuadruple P) 0) =
          BandPackingSymmetryVectorAction g
            (BandVectors.1 (r i.succ) (r 0)) := OrientedRightEndpointGeometry.phaseForward r i s
                U W Z hW hZ hWpos hWcent hZcent nonnegative zero a g0 P horient hzero hford hq
                negative hphase hphase1 hphase2 g horientg hfalse hfalse1 hfalse2 hW' hzeroAction
                hWford
    have phaseBackward :
        BandVectors.1 ((FordRecursiveQuadruple P) 0)
            ((FordRecursiveQuadruple P) k.succ) =
          BandPackingSymmetryVectorAction g
            (BandVectors.1 (r 0) (r i.succ)) := OrientedRightEndpointGeometry.phaseBackward r i s
                U W Z hW hZ hWpos hWcent hZcent nonnegative zero a g0 P horient hzero hford hq
                negative hphase hphase1 hphase2 g horientg hfalse hfalse1 hfalse2 hW' hzeroAction
                hWford phaseForward
    have centroidAction :
        TileCentroid (BandPackingSymmetryTileAction g W) -
            TileCentroid (BandPackingSymmetryTileAction g U) =
          (1 / 2 : Real) • GaussianRealPoint
            (BandPackingSymmetryVectorAction g
              ((⟨0, 1⟩ : GaussianInt) ^ s.val *
                (BandVectors.1 (r i.succ) (r 0) +
                  BandVectors.1 (r 0) (r i.succ)))) :=
                      OrientedRightEndpointGeometry.centroidAction r i s U W hWcent g0 hword g
                      hglift
    have actionAdd (x y : GaussianInt) :
        BandPackingSymmetryVectorAction g (x + y) =
          BandPackingSymmetryVectorAction g x +
            BandPackingSymmetryVectorAction g y := OrientedRightEndpointGeometry.actionAdd g0
                hword g hglift x y
    have actionCommute (x : GaussianInt) :
        BandPackingSymmetryVectorAction g
            ((⟨0, 1⟩ : GaussianInt) ^ s.val * x) =
          (⟨0, 1⟩ : GaussianInt) ^ s.val *
            BandPackingSymmetryVectorAction g x := OrientedRightEndpointGeometry.actionCommute r
                i s U W Z hZ hWcent hZcent nonnegative zero g0 hword g hglift centroidAction x
    have vectorIdentity :
        BandPackingSymmetryVectorAction g
              ((⟨0, 1⟩ : GaussianInt) ^ s.val *
                (BandVectors.1 (r i.succ) (r 0) +
                  BandVectors.1 (r 0) (r i.succ))) =
          (⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 ((FordRecursiveQuadruple P) k.succ)
                ((FordRecursiveQuadruple P) 0) +
              BandVectors.1 ((FordRecursiveQuadruple P) 0)
                ((FordRecursiveQuadruple P) k.succ)) :=
                    OrientedRightEndpointGeometry.vectorIdentity r i s a P g phaseForward
                    phaseBackward actionAdd actionCommute
    have transformedCentroid :
        TileCentroid (BandPackingSymmetryTileAction g W) -
            TileCentroid (BandPackingSymmetryTileAction g U) =
          (1 / 2 : Real) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ s.val *
              (BandVectors.1 ((FordRecursiveQuadruple P) k.succ)
                  ((FordRecursiveQuadruple P) 0) +
                BandVectors.1 ((FordRecursiveQuadruple P) 0)
                  ((FordRecursiveQuadruple P) k.succ))) :=
                      OrientedRightEndpointGeometry.transformedCentroid r i s U W a P g
                      centroidAction vectorIdentity
    have hUposFord : 0 < ((FordRecursiveQuadruple P) 0).1 :=
        OrientedRightEndpointGeometry.hUposFord r hUpos a g0 P horient g horientg tileCovariance
        hzeroAction
    have hWposFord : 0 < ((FordRecursiveQuadruple P) k.succ).1 :=
        OrientedRightEndpointGeometry.hWposFord r i s U W Z hW hZ hWpos hWcent hZcent nonnegative
        zero a g0 P horient hzero hford hq negative hphase hphase1 hphase2 g horientg hfalse
        hfalse1 hfalse2 tileCovariance hW' hzeroAction hWford phaseForward phaseBackward
        centroidAction vectorIdentity transformedCentroid
    have fordResult := FordOrientedChildParentRightEndpoint P hP k s
      (BandPackingSymmetryTileAction g U)
      (BandPackingSymmetryTileAction g W) hUford hWford hUposFord hWposFord
      transformedCentroid
    dsimp at fordResult
    have middleVector :
        BandPackingSymmetryVectorAction g
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (r 0) (r i.succ)
             else BandVectors.1 (r i.succ) (r 0))) =
          (⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 ((FordRecursiveQuadruple P) 0)
                ((FordRecursiveQuadruple P) k.succ)
             else
              BandVectors.1 ((FordRecursiveQuadruple P) k.succ)
                ((FordRecursiveQuadruple P) 0)) := OrientedRightEndpointGeometry.middleVector r i
                    s a P g phaseForward phaseBackward actionCommute
    have transport := (BandPackingSymmetryTilingTransport g).2.2.2.2.2.2.1
      U
      ((⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (r 0) (r i.succ)
         else BandVectors.1 (r i.succ) (r 0)))
    rw [← middleVector, ← transport] at fordResult
    have transformedTriple : Nonempty (ExactTileInterfaceTriple
        (BandPackingSymmetryTileAction g U)
        (BandPackingSymmetryTileAction g
          (TileTranslation U
            ((⟨0, 1⟩ : GaussianInt) ^ s.val *
              (if Even s.val then BandVectors.1 (r 0) (r i.succ)
               else BandVectors.1 (r i.succ) (r 0)))))
        (BandPackingSymmetryTileAction g W)) := @OrientedRightEndpointGeometry.transformedTriple r
            i s U W g fordResult
    exact (ExactTileInterfaceTriplePackingSymmetryCovariance g U
      (TileTranslation U
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (r 0) (r i.succ)
           else BandVectors.1 (r i.succ) (r 0)))) W).mpr transformedTriple

end ApollonianSuperharmonic

end
