/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty
public import LeanPool.ApollonianSuperharmonic.BoundaryFrameJoinGeometry
public import LeanPool.ApollonianSuperharmonic.BoundaryFrameRowGeometry

public import LeanPool.ApollonianSuperharmonic.BandRegularTileTouchingClassification
public import LeanPool.ApollonianSuperharmonic.BandVectorOrientationDichotomy
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryPlacement
public import LeanPool.ApollonianSuperharmonic.ParentVectorsInTilingLattice
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: P4458T1LargestParentRows]

/-!
# P4458T1LargestParentRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LargestParentGeometry

private theorem hq1 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 :
            Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin
            (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 -
            (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
            GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2
            - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 :
            ℕ))]) → (F.q F.slot.succ = p 0) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hstep
  have h := congrFun hstep 1
  simpa using h

private theorem hq2 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 :
            Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin
            (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 -
            (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
            GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2
            - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 :
            ℕ))]) → (F.q ((F.slot + 1).succ) = p 2) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hstep
  have h := congrFun hstep 2
  simpa using h

private theorem hq3 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 :
            Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin
            (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 -
            (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
            GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2
            - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 :
            ℕ))]) → (F.q ((F.slot + 2).succ) = p 3) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hstep
  have h := congrFun hstep 3
  simpa using h

private theorem houter :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 :
            Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin
            (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 -
            (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
            GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2
            - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 :
            ℕ))]) → (F.q 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2
            * (p 2).2 + 2 * (p 3).2 - (p 1).2)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hstep
  have h := congrFun hstep 0
  simpa using h

private theorem hCpositive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            4 → CircleCoordinates), (ProperBandQuadruple p) → ((F.q F.slot.succ = p 0) → (0 <
            (F.q F.slot.succ).1)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hp hq1
  rw [hq1]
  exact (ProperBandCurvatureStructure p hp).1

private theorem hnegativeSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), (0 < (F.q F.slot.succ).1) → (∃ s, PartialOdometerSlope
            (D.functions F.slot false) = some s) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hCpositive
  rcases D.slopes F.slot false with hz | ⟨root, child, hroot, hchild, _, _⟩
  · have hz' : (F.q F.slot.succ).1 = 0 := hz
    omega
  · exact ⟨child, hchild⟩

private theorem hrstep :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 :
            Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin
            (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 -
            (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
            GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2
            - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 :
            ℕ))]) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        r = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 *
            (p 3).2 - (p 1).2), p 0, p 2, p 3]) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hstep r
  simpa [r] using hstep

private theorem hvflip :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → (
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r hr I
  simpa [I] using
    (VectorRecursionLaws r hr.1).2.2.2.2 hr 0 |>.1

private theorem haflip :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → (
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r hr I
  simpa [I] using
    (VectorRecursionLaws r hr.1).2.2.2.2 hr 0 |>.2





private theorem hcenterVector :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 0) (r 1) = I * BandVectors.1
            (r 1) (r 0)) → ((w.re + x.re + y.re = 0) → ((w.im + x.im + y.im = 0) → (-w + I * w -
            BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1) = 2 * y)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I w x y hvrec hvflip hvsumRe hvsumIm
  rw [hvflip, hvrec]
  apply Zsqrtd.ext <;>
    norm_num [I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul] <;>
    omega

private theorem hyLattice :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → (
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (r 1 = C.1.1) → (y ∈ TilingLattice C)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r hr y hRparent
  have h := (ParentVectorsInTilingLattice r hr 0 C hRparent).1
  simpa [y] using h

private theorem hjoinBand :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        BandPrototile C.1.1 join ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r y u join
  simpa [join] using
    BandPrototileTranslation C.1.1 base (u + y) F.base_band





private theorem hjoinOdo :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), (0 < (F.q F.slot.succ).1) → ((TileOdometer (F.q
            F.slot.succ) (D.tiles F.slot false) (D.functions F.slot false)) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (BandPrototile C.1.1 join) → (((D.tiles F.slot false).cells = join.cells ∧ ((D.tiles
            F.slot false).cells = ∅ → (D.tiles F.slot false).anchor = join.anchor)) →
            (TileOdometer C.1.1 join (D.functions F.slot false))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hCpositive hselectedOdo r y u join
      hjoinBand hjoinCells
  exact PositiveCurvatureTileOdometerSupportTransport C.1.1
    (D.tiles F.slot false) join (D.functions F.slot false)
    (by rw [← F.parent]; exact hCpositive)
    (by rw [← F.parent]; exact hselectedOdo) hjoinBand hjoinCells.1


private theorem hjoinFootEq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        ((D.tiles F.slot false).cells = join.cells ∧ ((D.tiles F.slot false).cells = ∅ → (D.tiles
            F.slot false).anchor = join.anchor)) → (((D.tiles F.slot false).cells.Nonempty) →
            ((join.cells.Nonempty) → (FootprintVertices join = FootprintVertices (D.tiles F.slot
            false)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r y u join hjoinCells hUnonempty hJnonempty
  simp only [FootprintVertices, ite_eq_left hJnonempty, ite_eq_left hUnonempty]
  rw [hjoinCells.1]



private theorem hplusVector :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 0) (r 1) = I * BandVectors.1
            (r 1) (r 0)) → ((w.re + x.re + y.re = 0) → ((w.im + x.im + y.im = 0) → (BandVectors.1
            (r 1) (r 0) + BandVectors.1 (r 0) (r 1) + w - I * w = 2 * I * x)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I w x y hvrec hvflip hvsumRe hvsumIm
  rw [hvflip, hvrec]
  apply Zsqrtd.ext <;>
    norm_num [I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul] <;>
    omega


private theorem hPlusJoin :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = -(1 / 2 : ℝ) •
            (GaussianRealPoint w - (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) → (∀ (u
            : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileCentroid (D.tiles F.slot false) = TileCentroid join) → ((BandVectors.1 (r 1) (r 0) +
            BandVectors.1 (r 0) (r 1) + w - I * w = 2 * I * x) → ((TileCentroid Rplus -
            TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (r 1) (r 0) +
            BandVectors.1 (r 0) (r 1))) → (TileCentroid Rplus - TileCentroid join =
            GaussianRealPoint (I * x))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r I w x y hUcenter u join hjoinCenterEq
      hplusVector hPcenter
  rw [show TileCentroid Rplus - TileCentroid join =
    (TileCentroid Rplus - TileCentroid F.tile) -
      (TileCentroid join - TileCentroid F.tile) by
        ext <;> dsimp <;> ring]
  rw [hPcenter, ← hjoinCenterEq, hUcenter]
  have hRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) hplusVector
  have hIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) hplusVector
  apply Prod.ext
  · simp [GaussianRealPoint, I, w, x, Prod.smul_mk]
    norm_num at hRe ⊢
    linarith
  · simp [GaussianRealPoint, I, w, x, Prod.smul_mk]
    norm_num at hIm ⊢
    linarith

private theorem hSlopeInfo :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), (0 < (F.q F.slot.succ).1) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        ∃ root child : ℝ × ℝ, PartialOdometerSlope F.odometer = some root ∧ PartialOdometerSlope
            (D.functions F.slot false) = some child ∧ child.1 - root.1 = -(1 / 2 : ℝ) * (((wa.re
            : ℤ) : ℝ) - ((wa.im : ℤ) : ℝ)) ∧ child.2 - root.2 = -(1 / 2 : ℝ) * (((wa.im : ℤ) : ℝ)
            + ((wa.re : ℤ) : ℝ))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hCpositive r wa
  rcases D.slopes F.slot false with hzero | hdata
  · have hz := hzero
    omega
  · rcases hdata with ⟨root, child, hroot, hchild, hre, him⟩
    refine ⟨root, child, hroot, hchild, ?_, ?_⟩
    · simpa [r, wa] using hre
    · simpa [r, wa] using him

private theorem hDoffset :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        ∀ (rootSlope : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (joinSlope.1 - rootSlope.1 = -(1 / 2 : ℝ) *
            ((↑wa.re : ℝ) - (↑wa.im : ℝ))) → ((joinSlope.2 - rootSlope.2 = -(1 / 2 : ℝ) *
            ((↑wa.im : ℝ) + (↑wa.re : ℝ))) → (joinSlope - rootSlope = (-(1 / 2 : ℝ) * ((wa.re :
            ℤ) : ℝ) + (1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ), -(1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ) - (1 / 2
            : ℝ) * ((wa.re : ℤ) : ℝ)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa rootSlope joinSlope hjoinSlopeRe
      hjoinSlopeIm
  apply Prod.ext <;> dsimp <;> nlinarith [hjoinSlopeRe, hjoinSlopeIm]

private theorem hFminusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        F.minusSlope - F.outerSlope = ((1 / 2 : ℝ) * ((GaussianInt.toComplex (BandVectors.2 (r
            1) (r 0))).re - (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re), (1 / 2 : ℝ)
            * ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im - (GaussianInt.toComplex
            (BandVectors.2 (r 0) (r 1))).im)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r
  simpa [r, GaussianRealPoint, Prod.smul_mk] using F.minus_difference

private theorem hFplusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        F.plusSlope - F.outerSlope = ((1 / 2 : ℝ) * ((GaussianInt.toComplex (BandVectors.2 (r
            1) (r 0))).re + (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re), (1 / 2 : ℝ)
            * ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im + (GaussianInt.toComplex
            (BandVectors.2 (r 0) (r 1))).im)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r
  simpa [r, GaussianRealPoint, Prod.smul_mk] using F.plus_difference



private theorem ha10Re :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (BandVectors.2 (r 1) (r 0) = xa + I * ya) → ((BandVectors.2 (r 1) (r 0)).re = xa.re -
            ya.im) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa ya harec
  have h := congrArg (fun z : GaussianInt => z.re) harec
  have hh : (BandVectors.2 (r 1) (r 0)).re = xa.re + -ya.im := by
    simpa [I, xa, ya, Zsqrtd.re_mul, Zsqrtd.im_mul] using h
  linarith

private theorem ha10Im :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (BandVectors.2 (r 1) (r 0) = xa + I * ya) → ((BandVectors.2 (r 1) (r 0)).im = xa.im +
            ya.re) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa ya harec
  have h := congrArg (fun z : GaussianInt => z.im) harec
  simpa [I, xa, ya, Zsqrtd.re_mul, Zsqrtd.im_mul] using h

private theorem ha01Re :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0)) → (((BandVectors.2 (r 1) (r
            0)).im = xa.im + ya.re) → ((BandVectors.2 (r 0) (r 1)).re = xa.im + ya.re)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa ya haflip ha10Im
  have h := congrArg (fun z : GaussianInt => z.re) haflip
  simpa [I, ha10Im, Zsqrtd.re_mul, Zsqrtd.im_mul] using h

private theorem ha01Im :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0)) → (((BandVectors.2 (r 1) (r
            0)).re = xa.re - ya.im) → ((BandVectors.2 (r 0) (r 1)).im = -xa.re + ya.im)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa ya haflip ha10Re
  have h := congrArg (fun z : GaussianInt => z.im) haflip
  have hh : (BandVectors.2 (r 0) (r 1)).im = ya.im - xa.re := by
    simpa [I, ha10Re, Zsqrtd.re_mul, Zsqrtd.im_mul] using h
  linarith

private theorem hminusSlopeVector :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa.re + xa.re + ya.re = 0) → ((wa.im + xa.im + ya.im = 0) → (((BandVectors.2 (r 1) (r
            0)).re = xa.re - ya.im) → (((BandVectors.2 (r 1) (r 0)).im = xa.im + ya.re) →
            (((BandVectors.2 (r 0) (r 1)).re = xa.im + ya.re) → (((BandVectors.2 (r 0) (r 1)).im
            = -xa.re + ya.im) → (-(1 + I) * wa - BandVectors.2 (r 1) (r 0) + BandVectors.2 (r 0)
            (r 1) = 2 * ya)))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I wa xa ya hasumRe hasumIm ha10Re ha10Im
      ha01Re ha01Im
  apply Zsqrtd.ext
  · norm_num [I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul]
    rw [ha10Re, ha01Re]
    omega
  · norm_num [I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul]
    rw [ha10Im, ha01Im]
    omega

private theorem hplusSlopeVector :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa.re + xa.re + ya.re = 0) → ((wa.im + xa.im + ya.im = 0) → (((BandVectors.2 (r 1) (r
            0)).re = xa.re - ya.im) → (((BandVectors.2 (r 1) (r 0)).im = xa.im + ya.re) → ((1 -
            I) * BandVectors.2 (r 1) (r 0) + (1 + I) * wa = -2 * I * xa)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I wa xa ya hasumRe hasumIm ha10Re ha10Im
  apply Zsqrtd.ext
  · norm_num [I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul]
    rw [ha10Re]
    omega
  · norm_num [I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul]
    rw [ha10Im]
    omega

private theorem ha10ReC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ((BandVectors.2 (r 1) (r 0)).re = xa.re - ya.im) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).im = (z.im : ℝ)) → ((GaussianInt.toComplex (BandVectors.2
            (r 1) (r 0))).re = (GaussianInt.toComplex xa).re - (GaussianInt.toComplex ya).im))) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r xa ya ha10Re toRealRe toRealIm
  rw [toRealRe, toRealRe, toRealIm]
  exact_mod_cast ha10Re

private theorem ha10ImC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ((BandVectors.2 (r 1) (r 0)).im = xa.im + ya.re) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).im = (z.im : ℝ)) → ((GaussianInt.toComplex (BandVectors.2
            (r 1) (r 0))).im = (GaussianInt.toComplex xa).im + (GaussianInt.toComplex ya).re))) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r xa ya ha10Im toRealRe toRealIm
  rw [toRealIm, toRealIm, toRealRe]
  exact_mod_cast ha10Im

private theorem ha01ReC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ((BandVectors.2 (r 0) (r 1)).re = xa.im + ya.re) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).im = (z.im : ℝ)) → ((GaussianInt.toComplex (BandVectors.2
            (r 0) (r 1))).re = (GaussianInt.toComplex xa).im + (GaussianInt.toComplex ya).re))) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r xa ya ha01Re toRealRe toRealIm
  rw [toRealRe, toRealIm, toRealRe]
  exact_mod_cast ha01Re

private theorem ha01ImC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ((BandVectors.2 (r 0) (r 1)).im = -xa.re + ya.im) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).im = (z.im : ℝ)) → ((GaussianInt.toComplex (BandVectors.2
            (r 0) (r 1))).im = -(GaussianInt.toComplex xa).re + (GaussianInt.toComplex ya).im)))
            ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r xa ya ha01Im toRealRe toRealIm
  rw [toRealIm, toRealRe, toRealIm]
  exact_mod_cast ha01Im

private theorem hsumReC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa.re + xa.re + ya.re = 0) → ((∀ (z : GaussianInt), (GaussianInt.toComplex z).re = (z.re
            : ℝ)) → ((GaussianInt.toComplex wa).re + (GaussianInt.toComplex xa).re +
            (GaussianInt.toComplex ya).re = 0)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa ya hasumRe toRealRe
  rw [toRealRe, toRealRe, toRealRe]
  exact_mod_cast hasumRe

private theorem hsumImC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa.im + xa.im + ya.im = 0) → ((∀ (z : GaussianInt), (GaussianInt.toComplex z).im = (z.im
            : ℝ)) → ((GaussianInt.toComplex wa).im + (GaussianInt.toComplex xa).im +
            (GaussianInt.toComplex ya).im = 0)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa ya hasumIm toRealIm
  rw [toRealIm, toRealIm, toRealIm]
  exact_mod_cast hasumIm

private theorem hplusVectorRe' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa.re + xa.re + ya.re = 0) → ((wa.im + xa.im + ya.im = 0) → (((BandVectors.2 (r 1) (r
            0)).re = xa.re - ya.im) → (((BandVectors.2 (r 1) (r 0)).im = xa.im + ya.re) →
            ((BandVectors.2 (r 1) (r 0)).re + (BandVectors.2 (r 1) (r 0)).im + wa.re - wa.im = 2
            * xa.im)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa ya hasumRe hasumIm ha10Re ha10Im
  omega

private theorem hplusVectorIm' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa.re + xa.re + ya.re = 0) → ((wa.im + xa.im + ya.im = 0) → (((BandVectors.2 (r 1) (r
            0)).re = xa.re - ya.im) → (((BandVectors.2 (r 1) (r 0)).im = xa.im + ya.re) →
            ((BandVectors.2 (r 1) (r 0)).im - (BandVectors.2 (r 1) (r 0)).re + wa.im + wa.re = -2
            * xa.re)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa ya hasumRe hasumIm ha10Re ha10Im
  omega

private theorem hplusVectorReC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        (∀ (z : GaussianInt), (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).im = (z.im : ℝ)) → (((BandVectors.2 (r 1) (r 0)).re +
            (BandVectors.2 (r 1) (r 0)).im + wa.re - wa.im = 2 * xa.im) → ((GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).re + (GaussianInt.toComplex (BandVectors.2 (r 1) (r
            0))).im + (GaussianInt.toComplex wa).re - (GaussianInt.toComplex wa).im = 2 *
            (GaussianInt.toComplex xa).im))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa toRealRe toRealIm hplusVectorRe'
  rw [toRealRe, toRealIm, toRealRe, toRealIm, toRealIm]
  exact_mod_cast hplusVectorRe'

private theorem hplusVectorImC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        (∀ (z : GaussianInt), (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).im = (z.im : ℝ)) → (((BandVectors.2 (r 1) (r 0)).im -
            (BandVectors.2 (r 1) (r 0)).re + wa.im + wa.re = -2 * xa.re) →
            ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im - (GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).re + (GaussianInt.toComplex wa).im +
            (GaussianInt.toComplex wa).re = -2 * (GaussianInt.toComplex xa).re))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa toRealRe toRealIm hplusVectorIm'
  rw [toRealIm, toRealRe, toRealIm, toRealRe, toRealRe]
  exact_mod_cast hplusVectorIm'

private theorem hminusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (rootSlope : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (rootSlope = F.outerSlope) → ((joinSlope -
            rootSlope = (-(1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ) + (1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ), -(1
            / 2 : ℝ) * ((wa.im : ℤ) : ℝ) - (1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ))) → ((F.minusSlope -
            F.outerSlope = ((1 / 2 : ℝ) * ((GaussianInt.toComplex (BandVectors.2 (r 1) (r
            0))).re - (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re), (1 / 2 : ℝ) *
            ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im - (GaussianInt.toComplex
            (BandVectors.2 (r 0) (r 1))).im))) → ((-(1 + I) * wa - BandVectors.2 (r 1) (r 0) +
            BandVectors.2 (r 0) (r 1) = 2 * ya) → (((GaussianInt.toComplex (BandVectors.2 (r 1)
            (r 0))).re = (GaussianInt.toComplex xa).re - (GaussianInt.toComplex ya).im) →
            (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im = (GaussianInt.toComplex
            xa).im + (GaussianInt.toComplex ya).re) → (((GaussianInt.toComplex (BandVectors.2 (r
            0) (r 1))).re = (GaussianInt.toComplex xa).im + (GaussianInt.toComplex ya).re) →
            (((GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im = -(GaussianInt.toComplex
            xa).re + (GaussianInt.toComplex ya).im) → (((GaussianInt.toComplex wa).re +
            (GaussianInt.toComplex xa).re + (GaussianInt.toComplex ya).re = 0) →
            (((GaussianInt.toComplex wa).im + (GaussianInt.toComplex xa).im +
            (GaussianInt.toComplex ya).im = 0) → (joinSlope - F.minusSlope = GaussianRealPoint
            ya)))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I wa xa ya rootSlope joinSlope
      hrootSlopeEq hDoffset hFminusSlope hminusSlopeVector ha10ReC ha10ImC ha01ReC ha01ImC
      hsumReC hsumImC
  have h := hminusSlopeVector
  have hre := congrArg (fun z : GaussianInt => (z.re : ℝ)) h
  have him := congrArg (fun z : GaussianInt => (z.im : ℝ)) h
  have hDoffset' : joinSlope - rootSlope =
      (-(1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ) +
          (1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ),
       -(1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ) -
          (1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ)) := hDoffset
  have hFminusSlope' : F.minusSlope - rootSlope =
      ((1 / 2 : ℝ) *
          ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).re -
            (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re),
       (1 / 2 : ℝ) *
          ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im -
            (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im)) := by
    rw [hrootSlopeEq]
    exact hFminusSlope
  rw [show joinSlope - F.minusSlope =
    (joinSlope - rootSlope) - (F.minusSlope - rootSlope) by
      ext <;> dsimp <;> ring]
  rw [hDoffset', hFminusSlope']
  apply Prod.ext
  · simp [GaussianRealPoint]
    norm_num at hre ⊢
    linarith
  · simp [GaussianRealPoint]
    norm_num at him ⊢
    linarith

private theorem hplusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (rootSlope : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (rootSlope = F.outerSlope) → ((joinSlope -
            rootSlope = (-(1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ) + (1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ), -(1
            / 2 : ℝ) * ((wa.im : ℤ) : ℝ) - (1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ))) → ((F.plusSlope -
            F.outerSlope = ((1 / 2 : ℝ) * ((GaussianInt.toComplex (BandVectors.2 (r 1) (r
            0))).re + (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re), (1 / 2 : ℝ) *
            ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im + (GaussianInt.toComplex
            (BandVectors.2 (r 0) (r 1))).im))) → (((1 - I) * BandVectors.2 (r 1) (r 0) + (1 + I)
            * wa = -2 * I * xa) → (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).re =
            (GaussianInt.toComplex xa).re - (GaussianInt.toComplex ya).im) →
            (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im = (GaussianInt.toComplex
            xa).im + (GaussianInt.toComplex ya).re) → (((GaussianInt.toComplex (BandVectors.2 (r
            0) (r 1))).re = (GaussianInt.toComplex xa).im + (GaussianInt.toComplex ya).re) →
            (((GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im = -(GaussianInt.toComplex
            xa).re + (GaussianInt.toComplex ya).im) → (((GaussianInt.toComplex wa).re +
            (GaussianInt.toComplex xa).re + (GaussianInt.toComplex ya).re = 0) →
            (((GaussianInt.toComplex wa).im + (GaussianInt.toComplex xa).im +
            (GaussianInt.toComplex ya).im = 0) → (F.plusSlope - joinSlope = GaussianRealPoint
            (-I * xa))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I wa xa ya rootSlope joinSlope
      hrootSlopeEq hDoffset hFplusSlope hplusSlopeVector ha10ReC ha10ImC ha01ReC ha01ImC hsumReC
      hsumImC
  have hre := congrArg (fun z : GaussianInt => (z.re : ℝ)) hplusSlopeVector
  have him := congrArg (fun z : GaussianInt => (z.im : ℝ)) hplusSlopeVector
  have hDoffset' : joinSlope - rootSlope =
      (-(1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ) +
          (1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ),
       -(1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ) -
          (1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ)) := hDoffset
  have hFplusSlope' : F.plusSlope - rootSlope =
      ((1 / 2 : ℝ) *
          ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).re +
            (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re),
       (1 / 2 : ℝ) *
          ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im +
            (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im)) := by
    rw [hrootSlopeEq]
    exact hFplusSlope
  rw [show F.plusSlope - joinSlope =
    (F.plusSlope - rootSlope) - (joinSlope - rootSlope) by
      ext <;> dsimp <;> ring]
  rw [hFplusSlope', hDoffset']
  apply Prod.ext
  · simp [GaussianRealPoint]
    norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
    linarith [ha10ReC, ha01ReC, hsumReC, hsumImC,
      hplusVectorReC]
  · simp [GaussianRealPoint]
    norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
    linarith [ha10ImC, ha01ImC, hsumReC, hsumImC,
      hplusVectorImC]

private theorem hCgt1 :
    (by
      classical
      exact
        ∀ (C : BandCircle),
          ∀ (p : Fin 4 → CircleCoordinates),
            ProperBandQuadruple p → C.1.1 = p 0 → 1 < C.1.1.1
    ) := by
  classical
  intro C p hp hCcoord
  rw [hCcoord]
  have hfacts := ProperBandCurvatureStructure p hp
  have hpositive' : 0 < (p 0).1 := hfacts.1
  by_contra hn
  have hle : (p 0).1 ≤ 1 := by omega
  have hz : ∀ i : Fin 3, (p i.succ).1 = 0 := by
    intro i
    have hnonneg := hfacts.2.1 i
    have hbelow := hp.2 i
    have : (p i.succ).1 < 1 := by omega
    omega
  exact (by decide : (0 : Fin 3) ≠ 1) (hfacts.2.2 0 1 (hz 0) (hz 1))

private theorem hleftCent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileCentroid join = TileCentroid Rminus + GaussianRealPoint y) → (TileCentroid join -
            TileCentroid Rminus = GaussianRealPoint y) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r y u join hjoinCenter
  rw [hjoinCenter]
  simp []

private theorem hbasep :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer),
            (P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus) → (∀ (p : Fin 4
            → CircleCoordinates), (C.1.1 = p 0) → (BandPrototile (p 0) base)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hCcoord
  rw [← hCcoord]
  exact F.base_band

private theorem hleftTouch :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            4 → CircleCoordinates), (ProperBandQuadruple p) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (C.1.1 = p 0) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (join ∈ RegularTileFamily base (TilingLattice C)) → ((y = BandVectors.1 (p 2) (p 0)) →
            ((TileCentroid join - TileCentroid Rminus = GaussianRealPoint y) → ((BandPrototile (p
            0) base) → (TileTouching Rminus join)))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hp r y hCcoord u join hjoinFamily hy
      hleftCent hbasep
  apply (BandRegularTileTouchingClassification C p hp hCcoord.symm base
    hbasep Rminus join F.minus_family hjoinFamily).2
  exact ⟨1, Or.inl (by rw [hleftCent, hy]; norm_num [GaussianRealPoint])⟩

private theorem hrightTouch :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            4 → CircleCoordinates), (ProperBandQuadruple p) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (C.1.1 = p 0) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (join ∈ RegularTileFamily base (TilingLattice C)) → ((TileCentroid Rplus - TileCentroid
            join = GaussianRealPoint (I * x)) → (((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) = BandVectors.1 (p (3 : Fin
            (4 : ℕ))) (p (0 : Fin (4 : ℕ))) ∧ -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (p (0 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) = BandVectors.2 (p (3 : Fin (4 : ℕ))) (p
            (0 : Fin (4 : ℕ))) ∨ (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (p (0 : Fin
            (4 : ℕ))) (p (3 : Fin (4 : ℕ))) = -BandVectors.1 (p (3 : Fin (4 : ℕ))) (p (0 : Fin (4
            : ℕ))) ∧ -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (p (0 : Fin (4 : ℕ))) (p
            (3 : Fin (4 : ℕ))) = -BandVectors.2 (p (3 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ)))) →
            ((x = BandVectors.1 (p 0) (p 3)) → ((BandPrototile (p 0) base) → (((3 : Fin 4) =
            Fin.succ (2 : Fin 3)) → (TileTouching join Rplus)))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hp r I x y hCcoord u join hjoinFamily
      hPlusJoin horientation hx hbasep hindex3
  apply (BandRegularTileTouchingClassification C p hp hCcoord.symm base
    hbasep join Rplus hjoinFamily F.plus_family).2
  rcases horientation with horient | horient
  · refine ⟨2, Or.inl ?_⟩
    rw [hPlusJoin, hx, horient.1]
    simp [GaussianRealPoint, ← hindex3]
  · refine ⟨2, Or.inr ?_⟩
    rw [hPlusJoin, hx, horient.1]
    simp [GaussianRealPoint]

private theorem hleftSlope1 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (joinSlope : ℝ × ℝ), (joinSlope - F.minusSlope = GaussianRealPoint ya) → (joinSlope.1
            - F.minusSlope.1 = (ya.re : ℝ)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r ya joinSlope hleftSlope
  have h := congrArg Prod.fst hleftSlope
  simpa [GaussianRealPoint] using h

private theorem hleftSlope2 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (joinSlope : ℝ × ℝ), (joinSlope - F.minusSlope = GaussianRealPoint ya) → (joinSlope.2
            - F.minusSlope.2 = (ya.im : ℝ)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r ya joinSlope hleftSlope
  have h := congrArg Prod.snd hleftSlope
  simpa [GaussianRealPoint] using h

private theorem hleftAdjacent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (p : Fin 4 → CircleCoordinates),
            (ProperBandQuadruple p) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (C.1.1 = p 0) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileOdometer C.1.1 join (D.functions F.slot false)) → (∀ (joinSlope : ℝ × ℝ),
            (PartialOdometerSlope (D.functions F.slot false) = some joinSlope) → ((y =
            BandVectors.1 (p 2) (p 0)) → ((ya = BandVectors.2 (p 2) (p 0)) → ((TileCentroid join
            - TileCentroid Rminus = GaussianRealPoint y) → ((joinSlope.1 - F.minusSlope.1 =
            (ya.re : ℝ)) → ((joinSlope.2 - F.minusSlope.2 = (ya.im : ℝ)) → (LeftLatticeAdjacent
            C Rminus join hminus (D.functions F.slot false)))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D p hp r y ya hCcoord u join hjoinOdo
      joinSlope hjoinSlope hy haya hleftCent hleftSlope1 hleftSlope2
  refine ⟨F.minus_odo, hjoinOdo, F.minusSlope, joinSlope,
    F.slope_minus, hjoinSlope, ?_⟩
  · right
    refine ⟨p, 1, true, hp, hCcoord.symm, ?_, ?_, ?_⟩
    · rw [hleftCent, hy]
      norm_num [GaussianRealPoint]
    · simpa [haya] using hleftSlope1
    · simpa [haya] using hleftSlope2

private theorem hrightSlope1 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        ∀ (joinSlope : ℝ × ℝ), (F.plusSlope - joinSlope = GaussianRealPoint (-I * xa)) →
            (F.plusSlope.1 - joinSlope.1 = ((-I * xa).re : ℝ)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa joinSlope hrightSlope
  have h := congrArg Prod.fst hrightSlope
  simpa [GaussianRealPoint] using h

private theorem hrightSlope2 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        ∀ (joinSlope : ℝ × ℝ), (F.plusSlope - joinSlope = GaussianRealPoint (-I * xa)) →
            (F.plusSlope.2 - joinSlope.2 = ((-I * xa).im : ℝ)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa joinSlope hrightSlope
  have h := congrArg Prod.snd hrightSlope
  simpa [GaussianRealPoint] using h

private theorem hrightAdjacent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (p : Fin 4 → CircleCoordinates),
            (ProperBandQuadruple p) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        (C.1.1 = p 0) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileOdometer C.1.1 join (D.functions F.slot false)) → ((TileCentroid Rplus -
            TileCentroid join = GaussianRealPoint (I * x)) → (∀ (joinSlope : ℝ × ℝ),
            (PartialOdometerSlope (D.functions F.slot false) = some joinSlope) → (((⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) * BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) =
            BandVectors.1 (p (3 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) ∧ -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) =
            BandVectors.2 (p (3 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) ∨ (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) =
            -BandVectors.1 (p (3 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) ∧ -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) =
            -BandVectors.2 (p (3 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ)))) → ((x = BandVectors.1 (p
            0) (p 3)) → ((xa = BandVectors.2 (p 0) (p 3)) → (((3 : Fin 4) = Fin.succ (2 : Fin 3))
            → ((F.plusSlope.1 - joinSlope.1 = ((-I * xa).re : ℝ)) → ((F.plusSlope.2 -
            joinSlope.2 = ((-I * xa).im : ℝ)) → (LeftLatticeAdjacent C join Rplus (D.functions
            F.slot false) hplus))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D p hp r I x y xa hCcoord u join hjoinOdo
      hPlusJoin joinSlope hjoinSlope horientation hx hxa hindex3 hrightSlope1 hrightSlope2
  refine ⟨hjoinOdo, F.plus_odo, joinSlope, F.plusSlope,
    hjoinSlope, F.slope_plus, ?_⟩
  rcases horientation with horient | horient
  · right
    refine ⟨p, 2, true, hp, hCcoord.symm, ?_, ?_, ?_⟩
    · rw [hPlusJoin, hx, horient.1]
      simp [GaussianRealPoint, ← hindex3]
    · simpa [hindex3] using (calc
        F.plusSlope.1 - joinSlope.1 = ((-I * xa).re : ℝ) := hrightSlope1
        _ = ((BandVectors.2 (p 3) (p 0)).re : ℝ) := by
          rw [hxa]
          have ha := congrArg (fun z : GaussianInt => z.re) horient.2
          exact_mod_cast ha
        )
    · simpa [hindex3] using (calc
        F.plusSlope.2 - joinSlope.2 = ((-I * xa).im : ℝ) := hrightSlope2
        _ = ((BandVectors.2 (p 3) (p 0)).im : ℝ) := by
          rw [hxa]
          have ha := congrArg (fun z : GaussianInt => z.im) horient.2
          exact_mod_cast ha
        )
  · right
    refine ⟨p, 2, false, hp, hCcoord.symm, ?_, ?_, ?_⟩
    · rw [hPlusJoin, hx, horient.1]
      simp [GaussianRealPoint]
    · simpa [hindex3] using (calc
        F.plusSlope.1 - joinSlope.1 = ((-I * xa).re : ℝ) := hrightSlope1
        _ = -((BandVectors.2 (p 3) (p 0)).re : ℝ) := by
          rw [hxa]
          have ha := congrArg (fun z : GaussianInt => z.re) horient.2
          exact_mod_cast ha
        )
    · simpa [hindex3] using (calc
        F.plusSlope.2 - joinSlope.2 = ((-I * xa).im : ℝ) := hrightSlope2
        _ = -((BandVectors.2 (p 3) (p 0)).im : ℝ) := by
          rw [hxa]
          have ha := congrArg (fun z : GaussianInt => z.im) horient.2
          exact_mod_cast ha
        )

private theorem hMnonempty :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer),
            (P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus) → ((∀ (c :
            CircleCoordinates), ∀ (T : ProtoTile), 0 < c.1 → BandPrototile c T →
            T.cells.Nonempty) → ((1 < C.1.1.1) → (Rminus.cells.Nonempty))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F positiveCells hCgt1
  apply positiveCells C.1.1 Rminus (by omega)
  exact TileOdometerBandPrototile C.1.1 Rminus hminus F.minus_odo

private theorem hPnonempty :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer),
            (P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus) → ((∀ (c :
            CircleCoordinates), ∀ (T : ProtoTile), 0 < c.1 → BandPrototile c T →
            T.cells.Nonempty) → ((1 < C.1.1.1) → (Rplus.cells.Nonempty))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F positiveCells hCgt1
  apply positiveCells C.1.1 Rplus (by omega)
  exact TileOdometerBandPrototile C.1.1 Rplus hplus F.plus_odo

private theorem hleftNe :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileTouching Rminus join) → ((Rminus.cells.Nonempty) → (Rminus ≠ join)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r y u join hleftTouch hMnonempty heq
  have ht := hleftTouch
  rw [← heq] at ht
  rcases ht with h | h | h
  · exact hMnonempty.ne_empty ((Finset.disjoint_self_iff_empty _).mp h.2.2.1)
  · exact hMnonempty.ne_empty h.1
  · exact hMnonempty.ne_empty h.1

private theorem hrightNe :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileTouching join Rplus) → ((Rplus.cells.Nonempty) → (join ≠ Rplus)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r y u join hrightTouch hPnonempty heq
  have ht := hrightTouch
  rw [heq] at ht
  rcases ht with h | h | h
  · exact hPnonempty.ne_empty ((Finset.disjoint_self_iff_empty _).mp h.2.2.1)
  · exact hPnonempty.ne_empty h.1
  · exact hPnonempty.ne_empty h.1

private theorem leftString :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (p : Fin 4 → CircleCoordinates), (![F.q (0 : Fin (4
            : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
            ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 :
            GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2
            + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin
            (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → ((F.q F.slot.succ = p 0) →
            ((F.q ((F.slot + 1).succ) = p 2) → ((F.q ((F.slot + 2).succ) = p 3) → ((F.q 0 = (2 *
            (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
            3).2 - (p 1).2)) → ((0 < (F.q F.slot.succ).1) → (((F.q F.slot.succ).1 < (F.q 0).1) →
            ((AncestorOdometer (F.q F.slot.succ) F.outer.1.1 (D.tiles F.slot false) F.tile
                (D.functions F.slot false)
            F.odometer) → ((TileOdometer (F.q F.slot.succ) (D.tiles F.slot false) (D.functions
            F.slot false)) → ((∃ s, PartialOdometerSlope (D.functions F.slot false) = some s) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → ((r = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 *
            (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p 3]) → ((r 1 = p 0) → ((r
            2 = p 2) → ((r 3 = p 3) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (w + x + y = 0) → ((wa + xa + ya = 0) → ((BandVectors.1 (r 1) (r 0) = x - I * y) →
            ((BandVectors.2 (r 1) (r 0) = xa + I * ya) → ((BandVectors.1 (r 0) (r 1) = I *
            BandVectors.1 (r 1) (r 0)) → ((BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1)
            (r 0)) → ((BandPrototile (F.q F.slot.succ) (D.tiles F.slot false)) →
            ((FootprintVertices (D.tiles F.slot false) ⊆ FootprintVertices F.tile) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = (if false = true then
            (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (F.slot
            + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = -(1 / 2 : ℝ) •
            (GaussianRealPoint w - (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) →
            ((TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) → ((w.re + x.re + y.re = 0)
            → ((w.im + x.im + y.im = 0) → ((-w + I * w - BandVectors.1 (r 1) (r 0) +
            BandVectors.1 (r 0) (r 1) = 2 * y) → (((↑(-w + I * w - BandVectors.1 (r (1 : Fin (4 :
            ℕ))) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 :
            ℕ)))).re : ℝ) = (↑((2 : GaussianInt) * y).re : ℝ)) → (((↑(-w + I * w - BandVectors.1
            (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r
            (1 : Fin (4 : ℕ)))).im : ℝ) = (↑((2 : GaussianInt) * y).im : ℝ)) → ((TileCentroid
            (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y) → ((r 1 = C.1.1)
            → ((y ∈ TilingLattice C) → (∀ (u : ↥(TilingLattice C)), (Rminus = TileTranslation
            base (↑u : GaussianInt)) → ((∀ (y : ↥(TilingLattice C)), (fun (u : ↥(TilingLattice
            C)) => Rminus = TileTranslation base (↑u : GaussianInt)) y → y = u) → (
        let join : ProtoTile := TileTranslation base (u + y)
        (join = TileTranslation Rminus y) → ((BandPrototile C.1.1 join) → ((join ∈
            RegularTileFamily base (TilingLattice C)) → ((TileCentroid join = TileCentroid Rminus
            + GaussianRealPoint y) → ((TileCentroid (D.tiles F.slot false) = TileCentroid join) →
            ((BandPrototile C.1.1 (D.tiles F.slot false)) → (((D.tiles F.slot false).cells =
            join.cells ∧ ((D.tiles F.slot false).cells = ∅ → (D.tiles F.slot false).anchor =
            join.anchor)) → ((TileOdometer C.1.1 join (D.functions F.slot false)) →
            ((AncestorOdometer C.1.1 F.outer.1.1 join F.tile (D.functions F.slot false)
            F.odometer) → (((D.tiles F.slot false).cells.Nonempty) → ((join.cells.Nonempty) →
            ((FootprintVertices join = FootprintVertices (D.tiles F.slot false)) →
            ((FootprintVertices join ⊆ FootprintVertices F.tile) → ((BandSubtileOccurrence F.q
            F.tile F.slot false join) → ((BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1) +
            w - I * w = 2 * I * x) → ((TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1))) →
            ((TileCentroid Rplus - TileCentroid join = GaussianRealPoint (I * x)) → (∀ (rootSlope
            : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (PartialOdometerSlope F.odometer = some rootSlope) →
            ((PartialOdometerSlope (D.functions F.slot false) = some joinSlope) → ((joinSlope.1 -
            rootSlope.1 = -(1 / 2 : ℝ) * ((↑wa.re : ℝ) - (↑wa.im : ℝ))) → ((joinSlope.2 -
            rootSlope.2 = -(1 / 2 : ℝ) * ((↑wa.im : ℝ) + (↑wa.re : ℝ))) → ((rootSlope =
            F.outerSlope) → ((joinSlope - rootSlope = (-(1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ) + (1 / 2
            : ℝ) * ((wa.im : ℤ) : ℝ), -(1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ) - (1 / 2 : ℝ) * ((wa.re :
            ℤ) : ℝ))) → ((F.minusSlope - F.outerSlope = ((1 / 2 : ℝ) * ((GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).re - (GaussianInt.toComplex (BandVectors.2 (r 0) (r
            1))).re), (1 / 2 : ℝ) * ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im -
            (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im))) → ((F.plusSlope -
            F.outerSlope = ((1 / 2 : ℝ) * ((GaussianInt.toComplex (BandVectors.2 (r 1) (r
            0))).re + (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re), (1 / 2 : ℝ) *
            ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im + (GaussianInt.toComplex
            (BandVectors.2 (r 0) (r 1))).im))) → ((wa.re + xa.re + ya.re = 0) → ((wa.im + xa.im +
            ya.im = 0) → (((BandVectors.2 (r 1) (r 0)).re = xa.re - ya.im) → (((BandVectors.2 (r
            1) (r 0)).im = xa.im + ya.re) → (((BandVectors.2 (r 0) (r 1)).re = xa.im + ya.re) →
            (((BandVectors.2 (r 0) (r 1)).im = -xa.re + ya.im) → ((-(1 + I) * wa - BandVectors.2
            (r 1) (r 0) + BandVectors.2 (r 0) (r 1) = 2 * ya) → (((1 - I) * BandVectors.2 (r 1)
            (r 0) + (1 + I) * wa = -2 * I * xa) → (((GaussianInt.toComplex (BandVectors.2 (r 1)
            (r 0))).re = (GaussianInt.toComplex xa).re - (GaussianInt.toComplex ya).im) →
            (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im = (GaussianInt.toComplex
            xa).im + (GaussianInt.toComplex ya).re) → (((GaussianInt.toComplex (BandVectors.2 (r
            0) (r 1))).re = (GaussianInt.toComplex xa).im + (GaussianInt.toComplex ya).re) →
            (((GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im = -(GaussianInt.toComplex
            xa).re + (GaussianInt.toComplex ya).im) → (((GaussianInt.toComplex wa).re +
            (GaussianInt.toComplex xa).re + (GaussianInt.toComplex ya).re = 0) →
            (((GaussianInt.toComplex wa).im + (GaussianInt.toComplex xa).im +
            (GaussianInt.toComplex ya).im = 0) → (((((1 : GaussianInt) - I) * BandVectors.2 (r (1
            : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + ((1 : GaussianInt) + I) * wa).re = ((-2 :
            GaussianInt) * I * xa).re) → (((((1 : GaussianInt) - I) * BandVectors.2 (r (1 : Fin
            (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + ((1 : GaussianInt) + I) * wa).im = ((-2 :
            GaussianInt) * I * xa).im) → (((BandVectors.2 (r 1) (r 0)).re + (BandVectors.2 (r 1)
            (r 0)).im + wa.re - wa.im = 2 * xa.im) → (((BandVectors.2 (r 1) (r 0)).im -
            (BandVectors.2 (r 1) (r 0)).re + wa.im + wa.re = -2 * xa.re) →
            (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).re + (GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).im + (GaussianInt.toComplex wa).re -
            (GaussianInt.toComplex wa).im = 2 * (GaussianInt.toComplex xa).im) →
            (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im - (GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).re + (GaussianInt.toComplex wa).im +
            (GaussianInt.toComplex wa).re = -2 * (GaussianInt.toComplex xa).re) → ((joinSlope -
            F.minusSlope = GaussianRealPoint ya) → ((F.plusSlope - joinSlope =
            GaussianRealPoint (-I * xa)) → ((y = BandVectors.1 (p 2) (p 0)) → ((x = BandVectors.1
            (p 0) (p 3)) → ((xa = BandVectors.2 (p 0) (p 3)) → ((ya = BandVectors.2 (p 2) (p 0))
            → ((TileCentroid join - TileCentroid Rminus = GaussianRealPoint y) → ((TileTouching
            Rminus join) → ((TileTouching join Rplus) → ((joinSlope - F.minusSlope =
            GaussianRealPoint ya) → ((joinSlope.1 - F.minusSlope.1 = (ya.re : ℝ)) →
            ((joinSlope.2 - F.minusSlope.2 = (ya.im : ℝ)) → ((LeftLatticeAdjacent C Rminus join
            hminus (D.functions F.slot false)) → ((F.plusSlope - joinSlope = GaussianRealPoint
            (-I * xa)) → ((F.plusSlope.1 - joinSlope.1 = ((-I * xa).re : ℝ)) → ((F.plusSlope.2
            - joinSlope.2 = ((-I * xa).im : ℝ)) → ((LeftLatticeAdjacent C join Rplus (D.functions
            F.slot false) hplus) → ((Rminus.cells.Nonempty) → ((Rminus ≠ join) → ((join ≠ Rplus)
            → ((C.1.1.1 ≠ 1) → (TileString C orientation base Rminus join [Rminus,
            join])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            ))))))))))))))))))))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D p hstep hq1 hq2 hq3 houter hCpositive
      hstrict hselectedAnc hselectedOdo hnegativeSlope r hr hrstep hr1 hr2 hr3 I w x y wa xa ya
      hvsum hasum hvrec harec hvflip haflip hUband hUfoot hUcent hUcenter hMcenter hvsumRe
      hvsumIm hcenterVector hcenterRe hcenterIm hcenter hRparent hyLattice u huRminus
      hRminusUnique join hjoin_eq hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC
      hjoinCells hjoinOdo hjoinAncestor hUnonempty hJnonempty hjoinFootEq hjoinFoot
      hjoinOccurrence hplusVector hPcenter hPlusJoin rootSlope joinSlope hrootSlope hjoinSlope
      hjoinSlopeRe hjoinSlopeIm hrootSlopeEq hDoffset hFminusSlope hFplusSlope hasumRe hasumIm
      ha10Re ha10Im ha01Re ha01Im hminusSlopeVector hplusSlopeVector ha10ReC ha10ImC ha01ReC
      ha01ImC hsumReC hsumImC hplusVectorRe hplusVectorIm hplusVectorRe' hplusVectorIm'
      hplusVectorReC hplusVectorImC hminusSlope hplusSlope hy hx hxa haya hleftCent hleftTouch
      hrightTouch hleftSlope hleftSlope1 hleftSlope2 hleftAdjacent hrightSlope hrightSlope1
      hrightSlope2 hrightAdjacent hMnonempty hleftNe hrightNe hnonunit
  unfold TileString
  refine ⟨F.base_band, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa using hleftNe
  · intro T hT
    simp only [List.mem_cons] at hT
    rcases hT with hT | hT
    · rcases hT with rfl
      exact F.minus_family
    · rcases hT with hT | hT
      · rcases hT with rfl
        exact hjoinFamily
      · simp at hT
  · simpa [List.IsChain, List.isChain_pair, hnonunit] using hleftTouch
  · intro pre T post heq hpre hpost
    have hlen := congrArg List.length heq
    have hp : 1 ≤ pre.length := by
      cases pre with
      | nil => simp at hpre
      | cons x xs => simp
    have hq : 1 ≤ post.length := by
      cases post with
      | nil => simp at hpost
      | cons x xs => simp
    simp at hlen
    omega

private theorem rightString :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (p : Fin 4 → CircleCoordinates), (![F.q (0 : Fin (4
            : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
            ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 :
            GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2
            + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin
            (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → ((F.q F.slot.succ = p 0) →
            ((F.q ((F.slot + 1).succ) = p 2) → ((F.q ((F.slot + 2).succ) = p 3) → ((F.q 0 = (2 *
            (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
            3).2 - (p 1).2)) → ((0 < (F.q F.slot.succ).1) → (((F.q F.slot.succ).1 < (F.q 0).1) →
            ((AncestorOdometer (F.q F.slot.succ) F.outer.1.1 (D.tiles F.slot false) F.tile
                (D.functions F.slot false)
            F.odometer) → ((TileOdometer (F.q F.slot.succ) (D.tiles F.slot false) (D.functions
            F.slot false)) → ((∃ s, PartialOdometerSlope (D.functions F.slot false) = some s) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → ((r = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 *
            (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p 3]) → ((r 1 = p 0) → ((r
            2 = p 2) → ((r 3 = p 3) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (w + x + y = 0) → ((wa + xa + ya = 0) → ((BandVectors.1 (r 1) (r 0) = x - I * y) →
            ((BandVectors.2 (r 1) (r 0) = xa + I * ya) → ((BandVectors.1 (r 0) (r 1) = I *
            BandVectors.1 (r 1) (r 0)) → ((BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1)
            (r 0)) → ((BandPrototile (F.q F.slot.succ) (D.tiles F.slot false)) →
            ((FootprintVertices (D.tiles F.slot false) ⊆ FootprintVertices F.tile) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = (if false = true then
            (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (F.slot
            + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = -(1 / 2 : ℝ) •
            (GaussianRealPoint w - (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) →
            ((TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) → ((w.re + x.re + y.re = 0)
            → ((w.im + x.im + y.im = 0) → ((-w + I * w - BandVectors.1 (r 1) (r 0) +
            BandVectors.1 (r 0) (r 1) = 2 * y) → (((↑(-w + I * w - BandVectors.1 (r (1 : Fin (4 :
            ℕ))) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 :
            ℕ)))).re : ℝ) = (↑((2 : GaussianInt) * y).re : ℝ)) → (((↑(-w + I * w - BandVectors.1
            (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r
            (1 : Fin (4 : ℕ)))).im : ℝ) = (↑((2 : GaussianInt) * y).im : ℝ)) → ((TileCentroid
            (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y) → ((r 1 = C.1.1)
            → ((y ∈ TilingLattice C) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (join = TileTranslation Rminus y) → ((BandPrototile C.1.1 join) → ((join ∈
            RegularTileFamily base (TilingLattice C)) → ((TileCentroid join = TileCentroid Rminus
            + GaussianRealPoint y) → ((TileCentroid (D.tiles F.slot false) = TileCentroid join) →
            ((BandPrototile C.1.1 (D.tiles F.slot false)) → (((D.tiles F.slot false).cells =
            join.cells ∧ ((D.tiles F.slot false).cells = ∅ → (D.tiles F.slot false).anchor =
            join.anchor)) → ((TileOdometer C.1.1 join (D.functions F.slot false)) →
            ((AncestorOdometer C.1.1 F.outer.1.1 join F.tile (D.functions F.slot false)
            F.odometer) → (((D.tiles F.slot false).cells.Nonempty) → ((join.cells.Nonempty) →
            ((FootprintVertices join = FootprintVertices (D.tiles F.slot false)) →
            ((FootprintVertices join ⊆ FootprintVertices F.tile) → ((BandSubtileOccurrence F.q
            F.tile F.slot false join) → ((BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1) +
            w - I * w = 2 * I * x) → ((TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1))) →
            ((TileCentroid Rplus - TileCentroid join = GaussianRealPoint (I * x)) → (∀ (rootSlope
            : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (PartialOdometerSlope F.odometer = some rootSlope) →
            ((PartialOdometerSlope (D.functions F.slot false) = some joinSlope) → ((joinSlope.1 -
            rootSlope.1 = -(1 / 2 : ℝ) * ((↑wa.re : ℝ) - (↑wa.im : ℝ))) → ((joinSlope.2 -
            rootSlope.2 = -(1 / 2 : ℝ) * ((↑wa.im : ℝ) + (↑wa.re : ℝ))) → ((rootSlope =
            F.outerSlope) → ((joinSlope - rootSlope = (-(1 / 2 : ℝ) * ((wa.re : ℤ) : ℝ) + (1 / 2
            : ℝ) * ((wa.im : ℤ) : ℝ), -(1 / 2 : ℝ) * ((wa.im : ℤ) : ℝ) - (1 / 2 : ℝ) * ((wa.re :
            ℤ) : ℝ))) → ((F.minusSlope - F.outerSlope = ((1 / 2 : ℝ) * ((GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).re - (GaussianInt.toComplex (BandVectors.2 (r 0) (r
            1))).re), (1 / 2 : ℝ) * ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im -
            (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im))) → ((F.plusSlope -
            F.outerSlope = ((1 / 2 : ℝ) * ((GaussianInt.toComplex (BandVectors.2 (r 1) (r
            0))).re + (GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re), (1 / 2 : ℝ) *
            ((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im + (GaussianInt.toComplex
            (BandVectors.2 (r 0) (r 1))).im))) → ((wa.re + xa.re + ya.re = 0) → ((wa.im + xa.im +
            ya.im = 0) → (((BandVectors.2 (r 1) (r 0)).re = xa.re - ya.im) → (((BandVectors.2 (r
            1) (r 0)).im = xa.im + ya.re) → (((BandVectors.2 (r 0) (r 1)).re = xa.im + ya.re) →
            (((BandVectors.2 (r 0) (r 1)).im = -xa.re + ya.im) → ((-(1 + I) * wa - BandVectors.2
            (r 1) (r 0) + BandVectors.2 (r 0) (r 1) = 2 * ya) → (((1 - I) * BandVectors.2 (r 1)
            (r 0) + (1 + I) * wa = -2 * I * xa) → (((GaussianInt.toComplex (BandVectors.2 (r 1)
            (r 0))).re = (GaussianInt.toComplex xa).re - (GaussianInt.toComplex ya).im) →
            (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im = (GaussianInt.toComplex
            xa).im + (GaussianInt.toComplex ya).re) → (((GaussianInt.toComplex (BandVectors.2 (r
            0) (r 1))).re = (GaussianInt.toComplex xa).im + (GaussianInt.toComplex ya).re) →
            (((GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im = -(GaussianInt.toComplex
            xa).re + (GaussianInt.toComplex ya).im) → (((GaussianInt.toComplex wa).re +
            (GaussianInt.toComplex xa).re + (GaussianInt.toComplex ya).re = 0) →
            (((GaussianInt.toComplex wa).im + (GaussianInt.toComplex xa).im +
            (GaussianInt.toComplex ya).im = 0) → (((((1 : GaussianInt) - I) * BandVectors.2 (r (1
            : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + ((1 : GaussianInt) + I) * wa).re = ((-2 :
            GaussianInt) * I * xa).re) → (((((1 : GaussianInt) - I) * BandVectors.2 (r (1 : Fin
            (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + ((1 : GaussianInt) + I) * wa).im = ((-2 :
            GaussianInt) * I * xa).im) → (((BandVectors.2 (r 1) (r 0)).re + (BandVectors.2 (r 1)
            (r 0)).im + wa.re - wa.im = 2 * xa.im) → (((BandVectors.2 (r 1) (r 0)).im -
            (BandVectors.2 (r 1) (r 0)).re + wa.im + wa.re = -2 * xa.re) →
            (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).re + (GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).im + (GaussianInt.toComplex wa).re -
            (GaussianInt.toComplex wa).im = 2 * (GaussianInt.toComplex xa).im) →
            (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im - (GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).re + (GaussianInt.toComplex wa).im +
            (GaussianInt.toComplex wa).re = -2 * (GaussianInt.toComplex xa).re) → ((joinSlope -
            F.minusSlope = GaussianRealPoint ya) → ((F.plusSlope - joinSlope =
            GaussianRealPoint (-I * xa)) → ((y = BandVectors.1 (p 2) (p 0)) → ((x = BandVectors.1
            (p 0) (p 3)) → ((xa = BandVectors.2 (p 0) (p 3)) → ((ya = BandVectors.2 (p 2) (p 0))
            → ((TileCentroid join - TileCentroid Rminus = GaussianRealPoint y) → ((TileTouching
            Rminus join) → ((TileTouching join Rplus) → ((joinSlope - F.minusSlope =
            GaussianRealPoint ya) → ((joinSlope.1 - F.minusSlope.1 = (ya.re : ℝ)) →
            ((joinSlope.2 - F.minusSlope.2 = (ya.im : ℝ)) → ((LeftLatticeAdjacent C Rminus join
            hminus (D.functions F.slot false)) → ((F.plusSlope - joinSlope = GaussianRealPoint
            (-I * xa)) → ((F.plusSlope.1 - joinSlope.1 = ((-I * xa).re : ℝ)) → ((F.plusSlope.2
            - joinSlope.2 = ((-I * xa).im : ℝ)) → ((LeftLatticeAdjacent C join Rplus (D.functions
            F.slot false) hplus) → ((Rplus.cells.Nonempty) → ((Rminus ≠ join) → ((join ≠ Rplus) →
            ((C.1.1.1 ≠ 1) → ((TileString C orientation base Rminus join [Rminus, join]) →
            (TileString C orientation base join Rplus [join,
            Rplus]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            ))))))))))))))))))))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D p hstep hq1 hq2 hq3 houter hCpositive
      hstrict hselectedAnc hselectedOdo hnegativeSlope r hr hrstep hr1 hr2 hr3 I w x y wa xa ya
      hvsum hasum hvrec harec hvflip haflip hUband hUfoot hUcent hUcenter hMcenter hvsumRe
      hvsumIm hcenterVector hcenterRe hcenterIm hcenter hRparent hyLattice u join hjoin_eq
      hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC hjoinCells hjoinOdo hjoinAncestor
      hUnonempty hJnonempty hjoinFootEq hjoinFoot hjoinOccurrence hplusVector hPcenter hPlusJoin
      rootSlope joinSlope hrootSlope hjoinSlope hjoinSlopeRe hjoinSlopeIm hrootSlopeEq hDoffset
      hFminusSlope hFplusSlope hasumRe hasumIm ha10Re ha10Im ha01Re ha01Im hminusSlopeVector
      hplusSlopeVector ha10ReC ha10ImC ha01ReC ha01ImC hsumReC hsumImC hplusVectorRe
      hplusVectorIm hplusVectorRe' hplusVectorIm' hplusVectorReC hplusVectorImC hminusSlope
      hplusSlope hy hx hxa haya hleftCent hleftTouch hrightTouch hleftSlope hleftSlope1
      hleftSlope2 hleftAdjacent hrightSlope hrightSlope1 hrightSlope2 hrightAdjacent hPnonempty
      hleftNe hrightNe hnonunit leftString
  unfold TileString
  refine ⟨F.base_band, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa using hrightNe
  · intro T hT
    simp only [List.mem_cons] at hT
    rcases hT with hT | hT
    · rcases hT with rfl
      exact hjoinFamily
    · rcases hT with hT | hT
      · rcases hT with rfl
        exact F.plus_family
      · simp at hT
  · simpa [List.IsChain, List.isChain_pair, hnonunit] using hrightTouch
  · intro pre T post heq hpre hpost
    have hlen := congrArg List.length heq
    have hp : 1 ≤ pre.length := by
      cases pre with
      | nil => simp at hpre
      | cons x xs => simp
    have hq : 1 ≤ post.length := by
      cases post with
      | nil => simp at hpost
      | cons x xs => simp
    simp at hlen
    omega

end LargestParentGeometry

namespace LargestParentConclusion

private theorem largestParentCertificate :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (p : Fin 4 → CircleCoordinates),
            (ProperBandQuadruple p) → ((![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0
            : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
            ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
            GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2
            - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 :
            ℕ))]) → ((F.q F.slot.succ = p 0) → ((F.q ((F.slot + 1).succ) = p 2) → ((F.q ((F.slot
            + 2).succ) = p 3) → ((F.q (0 : Fin (4 : ℕ)) = ((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2
            : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 :
            ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin
            (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2))
            → (((0 : ℤ) < (F.q F.slot.succ).1) → (((F.q F.slot.succ).1 < (F.q 0).1) →
            ((AncestorOdometer (F.q F.slot.succ) F.outer.1.1 (D.tiles F.slot false) F.tile
                (D.functions F.slot false)
            F.odometer) → ((TileOdometer (F.q F.slot.succ) (D.tiles F.slot false) (D.functions
            F.slot false)) → ((∃ (s : ℝ × ℝ), PartialOdometerSlope (D.functions F.slot false) =
            some s) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → ((
        let r := ![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ,
            F.q (F.slot + (2 : Fin (3 : ℕ))).succ]; r = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2
            : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 :
            ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin
            (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2),
            p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → ((r 1 = p 0) → ((r
            2 = p 2) → ((r 3 = p 3) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (w + x + y = 0) → ((wa + xa + ya = 0) → ((BandVectors.1 (r 1) (r 0) = x - I * y) →
            ((BandVectors.2 (r 1) (r 0) = xa + I * ya) → ((
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt); BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            = I * BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))) → ((
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt); BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            = -I * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 :
            Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))) → ((BandPrototile (F.q
            F.slot.succ) (D.tiles F.slot false)) → ((FootprintVertices (D.tiles F.slot false) ⊆
            FootprintVertices F.tile) → ((TileCentroid (D.tiles F.slot false) - TileCentroid
            F.tile = (if false = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) → ((TileCentroid (D.tiles F.slot false) -
            TileCentroid F.tile = -(1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))) - (-(GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ))))).2, (GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ))))).1))) → ((
        let r := ![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ,
            F.q (F.slot + (2 : Fin (3 : ℕ))).succ]; TileCentroid Rminus - TileCentroid F.tile =
            (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 :
            ℕ))) - BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))))) → (((BandVectors.1
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).re + (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).re + (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).re = (0 : ℤ)) →
            (((BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).im + (BandVectors.1 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ)))).im + (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).im = (0 : ℤ)) →
            ((-BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) - BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))
            + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) = (2 : GaussianInt) * BandVectors.1
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ)))) → (((↑(-BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            - BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).re : ℝ) = (↑((2 : GaussianInt) * BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).re : ℝ)) → (((↑(-BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) * BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) - BandVectors.1
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).im : ℝ) = (↑((2 : GaussianInt) * BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).im : ℝ)) → ((TileCentroid (D.tiles F.slot false) - TileCentroid Rminus =
            GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))) → ((C.1.1 = p
            0) → ((r 1 = C.1.1) → ((BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) ∈ TilingLattice
            C) → (∀ (u : ↥(TilingLattice C)), (Rminus = TileTranslation base (↑u : GaussianInt))
            → ((∀ (y : ↥(TilingLattice C)), (fun (u : ↥(TilingLattice C)) => Rminus =
            TileTranslation base (↑u : GaussianInt)) y → y = u) → (
        let join : ProtoTile := TileTranslation base (u + y)
        (join = TileTranslation Rminus y) → ((
        let join := TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ)))); BandPrototile C.1.1 join) → ((
        let join := TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ)))); join ∈ RegularTileFamily base (TilingLattice C)) → ((TileCentroid
            (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ))))) = TileCentroid Rminus + GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ))))) → ((TileCentroid (D.tiles F.slot false) = TileCentroid (TileTranslation base
            ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))))) →
            ((BandPrototile C.1.1 (D.tiles F.slot false)) → (((D.tiles F.slot false).cells =
            join.cells ∧ ((D.tiles F.slot false).cells = ∅ → (D.tiles F.slot false).anchor =
            join.anchor)) → ((TileOdometer C.1.1 (TileTranslation base ((↑u : GaussianInt) +
            BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))) (D.functions F.slot false)) →
            ((AncestorOdometer C.1.1 F.outer.1.1
            (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ))))) F.tile (D.functions F.slot false) F.odometer) → ((∀ (c : CircleCoordinates), ∀
            (T : ProtoTile), (0 : ℤ) < c.1 → BandPrototile c T → Finset.Nonempty T.cells) →
            (((D.tiles F.slot false).cells.Nonempty) → ((join.cells.Nonempty) →
            ((FootprintVertices (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))) = FootprintVertices (D.tiles F.slot false)) →
            ((FootprintVertices (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))) ⊆ FootprintVertices F.tile) → ((BandSubtileOccurrence
            F.q F.tile F.slot false (TileTranslation base ((↑u : GaussianInt) + BandVectors.1
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ)))))) → ((BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))
            + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            = (2 : GaussianInt) * (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))) → ((
        let r := ![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ,
            F.q (F.slot + (2 : Fin (3 : ℕ))).succ]; TileCentroid Rplus - TileCentroid F.tile = (1
            / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 :
            ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))))) → ((TileCentroid
            Rplus - TileCentroid (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))) = GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))))) → (∀ (rootSlope : ℝ × ℝ), ∀
            (joinSlope : ℝ × ℝ), (PartialOdometerSlope F.odometer = some rootSlope) →
            ((PartialOdometerSlope (D.functions F.slot false) = some joinSlope) → ((joinSlope.1 -
            rootSlope.1 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ)))).re : ℝ) - (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).im : ℝ))) →
            ((joinSlope.2 - rootSlope.2 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ)))).im : ℝ) + (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).re : ℝ))) →
            ((rootSlope = F.outerSlope) → ((joinSlope - rootSlope = (-(1 / 2 : ℝ) *
            (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).re : ℝ) + (1 / 2 : ℝ) * (↑(BandVectors.2
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).im : ℝ), -(1 / 2 : ℝ) * (↑(BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).im : ℝ) - (1 / 2 : ℝ) * (↑(BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).re : ℝ))) → ((
        let r := ![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ,
            F.q (F.slot + (2 : Fin (3 : ℕ))).succ]; F.minusSlope - F.outerSlope = ((1 / 2 : ℝ)
            * (((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (r (1 : Fin (4 : ℕ))) (r
            (0 : Fin (4 : ℕ))))).re - ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))))).re), (1 / 2 : ℝ) *
            (((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (r (1 : Fin (4 : ℕ))) (r
            (0 : Fin (4 : ℕ))))).im - ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))))).im))) → ((
        let r := ![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ,
            F.q (F.slot + (2 : Fin (3 : ℕ))).succ]; F.plusSlope - F.outerSlope = ((1 / 2 : ℝ) *
            (((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (r (1 : Fin (4 : ℕ))) (r
            (0 : Fin (4 : ℕ))))).re + ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))))).re), (1 / 2 : ℝ) *
            (((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (r (1 : Fin (4 : ℕ))) (r
            (0 : Fin (4 : ℕ))))).im + ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))))).im))) → (((BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).re + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).re + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).re = (0 : ℤ)) →
            (((BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).im = (0 : ℤ)) →
            (((BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))).re = (BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ)))).re - (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).im) → (((BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ)))).im = (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).re) → (((BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ)))).re = (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).re) → (((BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ)))).im = -(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).re + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).im) → ((-((1 : GaussianInt) +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            - BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) + BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            = (2 : GaussianInt) * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))) → ((((1 :
            GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (![F.q (0 : Fin (4
            : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4
            : ℕ))) + ((1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) = (-2 : GaussianInt) * (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))) → ((((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))))).re =
            ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ))))).re - ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ))))).im) → ((((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))))).im = ((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))))).im + ((GaussianInt.toComplex : GaussianInt →
            ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))).re) → ((((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))).re =
            ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ))))).im + ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ))))).re) → ((((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))).im = -((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))))).re + ((GaussianInt.toComplex : GaussianInt →
            ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))).im) → ((((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))))).re +
            ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ))))).re + ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ))))).re = (0 : ℝ)) → ((((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))))).im + ((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))))).im + ((GaussianInt.toComplex : GaussianInt →
            ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))).im = (0 : ℝ)) → (((((1 : GaussianInt) -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))
            + ((1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).re = ((-2 : GaussianInt) * (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))).re) → (((((1 : GaussianInt) -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))
            + ((1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).im = ((-2 : GaussianInt) * (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))).im) → (((BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ)))).re + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 :
            ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).re - (BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).im = (2 : ℤ) * (BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ)))).im) → (((BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))).im - (BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ)))).re + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).re = (-2 : ℤ) * (BandVectors.2
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).re) → ((((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))))).re + ((GaussianInt.toComplex : GaussianInt →
            ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))))).im + ((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))))).re -
            ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ))))).im = (2 : ℝ) * ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))))).im) → ((((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))))).im - ((GaussianInt.toComplex : GaussianInt →
            ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))))).re + ((GaussianInt.toComplex :
            GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))))).im +
            ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ))))).re = (-2 : ℝ) * ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))))).re) → ((joinSlope - F.minusSlope = GaussianRealPoint
            ya) → ((F.plusSlope - joinSlope = GaussianRealPoint (-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))))) → (Nonempty
            (P4458T1BoundaryPlacement F
            D)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            )))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D p hp hstep hq1 hq2 hq3 houter hCpositive
      hstrict hselectedAnc hselectedOdo hnegativeSlope r hr hrstep hr1 hr2 hr3 I w x y wa xa ya
      hvsum hasum hvrec harec hvflip haflip hUband hUfoot hUcent hUcenter hMcenter hvsumRe
      hvsumIm hcenterVector hcenterRe hcenterIm hcenter hCcoord hRparent hyLattice u huRminus
      hRminusUnique join hjoin_eq hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC
      hjoinCells hjoinOdo hjoinAncestor positiveCells hUnonempty hJnonempty hjoinFootEq hjoinFoot
      hjoinOccurrence hplusVector hPcenter hPlusJoin rootSlope joinSlope hrootSlope hjoinSlope
      hjoinSlopeRe hjoinSlopeIm hrootSlopeEq hDoffset hFminusSlope hFplusSlope hasumRe hasumIm
      ha10Re ha10Im ha01Re ha01Im hminusSlopeVector hplusSlopeVector ha10ReC ha10ImC ha01ReC
      ha01ImC hsumReC hsumImC hplusVectorRe hplusVectorIm hplusVectorRe' hplusVectorIm'
      hplusVectorReC hplusVectorImC hminusSlope hplusSlope
  have hCgt1 := LargestParentGeometry.hCgt1 C p hp
      hCcoord
  have hpTangency : BandTangency (p 0) (p 3) := by
    exact ⟨p, hp.1, 0, 3, by decide, rfl, rfl⟩
  have horientation := BandVectorOrientationDichotomy (p 0) (p 3) hpTangency
  have hy : y = BandVectors.1 (p 2) (p 0) := by
    simp [y, hr2, hr1]
  have hx : x = BandVectors.1 (p 0) (p 3) := by
    simp [x, hr1, hr3]
  have hxa : xa = BandVectors.2 (p 0) (p 3) := by
    simp [xa, hr1, hr3]
  have haya : ya = BandVectors.2 (p 2) (p 0) := by
    simp [ya, hr2, hr1]
  have hleftCent := LargestParentGeometry.hleftCent C orientation base Rminus Rplus hminus hplus
      F u hjoinCenter
  have hbasep := LargestParentGeometry.hbasep C orientation base Rminus Rplus hminus hplus F p
      hCcoord
  have hindex3 : (3 : Fin 4) = Fin.succ (2 : Fin 3) := by decide
  have hleftTouch := LargestParentGeometry.hleftTouch C orientation base Rminus Rplus hminus
      hplus F p hp hCcoord u hjoinFamily hy hleftCent hbasep
  have hrightTouch := LargestParentGeometry.hrightTouch C orientation base Rminus Rplus hminus
      hplus F p hp hCcoord u hjoinFamily hPlusJoin horientation hx hbasep hindex3
  have hleftSlope : joinSlope - F.minusSlope = GaussianRealPoint ya := by
    rw [hminusSlope]
  have hleftSlope1 := LargestParentGeometry.hleftSlope1 C orientation base Rminus Rplus hminus
      hplus F joinSlope hleftSlope
  have hleftSlope2 := LargestParentGeometry.hleftSlope2 C orientation base Rminus Rplus hminus
      hplus F joinSlope hleftSlope
  have hleftAdjacent := LargestParentGeometry.hleftAdjacent C orientation base Rminus Rplus
      hminus hplus F D p hp hCcoord u hjoinOdo joinSlope hjoinSlope hy haya hleftCent hleftSlope1
      hleftSlope2
  have hrightSlope : F.plusSlope - joinSlope = GaussianRealPoint (-I * xa) := hplusSlope
  have hrightSlope1 := LargestParentGeometry.hrightSlope1 C orientation base Rminus Rplus hminus
      hplus F joinSlope hrightSlope
  have hrightSlope2 := LargestParentGeometry.hrightSlope2 C orientation base Rminus Rplus hminus
      hplus F joinSlope hrightSlope
  have hrightAdjacent := LargestParentGeometry.hrightAdjacent C orientation base Rminus Rplus
      hminus hplus F D p hp hCcoord u hjoinOdo hPlusJoin joinSlope hjoinSlope horientation hx hxa
      hindex3 hrightSlope1 hrightSlope2
  have hMnonempty := LargestParentGeometry.hMnonempty C orientation base Rminus Rplus hminus
      hplus F positiveCells hCgt1
  have hPnonempty := LargestParentGeometry.hPnonempty C orientation base Rminus Rplus hminus
      hplus F positiveCells hCgt1
  have hleftNe := LargestParentGeometry.hleftNe C orientation base Rminus Rplus hminus hplus F u
      hleftTouch hMnonempty
  have hrightNe := LargestParentGeometry.hrightNe C orientation base Rminus Rplus hminus hplus F
      u hrightTouch hPnonempty
  have hnonunit : C.1.1.1 ≠ 1 := by omega
  have leftString := LargestParentGeometry.leftString C orientation base Rminus Rplus hminus
      hplus F D p hstep hq1 hq2 hq3 houter hCpositive hstrict hselectedAnc hselectedOdo
      hnegativeSlope hr hrstep hr1 hr2 hr3 hvsum hasum hvrec harec hvflip haflip hUband hUfoot
      hUcent hUcenter hMcenter hvsumRe hvsumIm hcenterVector hcenterRe hcenterIm hcenter hRparent
      hyLattice u huRminus hRminusUnique hjoin_eq hjoinBand hjoinFamily hjoinCenter hjoinCenterEq
      hUbandC hjoinCells hjoinOdo hjoinAncestor hUnonempty hJnonempty hjoinFootEq hjoinFoot
      hjoinOccurrence hplusVector hPcenter hPlusJoin rootSlope joinSlope hrootSlope hjoinSlope
      hjoinSlopeRe hjoinSlopeIm hrootSlopeEq hDoffset hFminusSlope hFplusSlope hasumRe hasumIm
      ha10Re ha10Im ha01Re ha01Im hminusSlopeVector hplusSlopeVector ha10ReC ha10ImC ha01ReC
      ha01ImC hsumReC hsumImC hplusVectorRe hplusVectorIm hplusVectorRe' hplusVectorIm'
      hplusVectorReC hplusVectorImC hminusSlope hplusSlope hy hx hxa haya hleftCent hleftTouch
      hrightTouch hleftSlope hleftSlope1 hleftSlope2 hleftAdjacent hrightSlope hrightSlope1
      hrightSlope2 hrightAdjacent hMnonempty hleftNe hrightNe hnonunit
  refine ⟨⟨join, hjoinCells.1.symm, hjoinOdo, hjoinAncestor,
    hjoinOccurrence, .direct leftString hleftAdjacent,
    .direct (LargestParentGeometry.rightString C orientation base Rminus Rplus hminus hplus F D p
        hstep hq1 hq2 hq3 houter hCpositive hstrict hselectedAnc hselectedOdo hnegativeSlope hr
        hrstep hr1 hr2 hr3 hvsum hasum hvrec harec hvflip haflip hUband hUfoot hUcent hUcenter
        hMcenter hvsumRe hvsumIm hcenterVector hcenterRe hcenterIm hcenter hRparent hyLattice u
        hjoin_eq hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC hjoinCells hjoinOdo
        hjoinAncestor hUnonempty hJnonempty hjoinFootEq hjoinFoot hjoinOccurrence hplusVector
        hPcenter hPlusJoin rootSlope joinSlope hrootSlope hjoinSlope hjoinSlopeRe hjoinSlopeIm
        hrootSlopeEq hDoffset hFminusSlope hFplusSlope hasumRe hasumIm ha10Re ha10Im ha01Re
        ha01Im hminusSlopeVector hplusSlopeVector ha10ReC ha10ImC ha01ReC ha01ImC hsumReC hsumImC
        hplusVectorRe hplusVectorIm hplusVectorRe' hplusVectorIm' hplusVectorReC hplusVectorImC
        hminusSlope hplusSlope hy hx hxa haya hleftCent hleftTouch hrightTouch hleftSlope
        hleftSlope1 hleftSlope2 hleftAdjacent hrightSlope hrightSlope1 hrightSlope2
        hrightAdjacent hPnonempty hleftNe hrightNe hnonunit leftString) hrightAdjacent⟩⟩

end LargestParentConclusion

theorem P4458T1LargestParentRows
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (a : Fin 3) (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (hstep : ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3])
    (selected : F.slot = a) :
    Nonempty (P4458T1BoundaryPlacement F D) := by
-- BODY
  classical
  subst a
  have hq1 : F.q F.slot.succ = p 0 := LargestParentGeometry.hq1 C orientation base Rminus Rplus
      hminus hplus F p hstep
  have hq2 : F.q ((F.slot + 1).succ) = p 2 := LargestParentGeometry.hq2 C orientation base Rminus
      Rplus hminus hplus F p hstep
  have hq3 : F.q ((F.slot + 2).succ) = p 3 := LargestParentGeometry.hq3 C orientation base Rminus
      Rplus hminus hplus F p hstep
  have houter := LargestParentGeometry.houter C orientation base Rminus Rplus hminus hplus F p hstep
  have hCpositive := LargestParentGeometry.hCpositive C orientation base Rminus Rplus hminus
      hplus F p hp hq1
  have hstrict : (F.q F.slot.succ).1 < (F.q 0).1 := F.proper.2 F.slot
  have hselectedAnc := D.ancestors F.slot false hCpositive
  have hselectedOdo := D.odometers F.slot false
  have hselectedOcc := D.occurrences F.slot false
  have hnegativeSlope := LargestParentGeometry.hnegativeSlope C orientation base Rminus Rplus
      hminus hplus F D hCpositive
  let r : Fin 4 → CircleCoordinates :=
    ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
      F.q ((F.slot + 2).succ)]
  have hr : ProperBandQuadruple r :=
    BoundaryFrameRowGeometry.presentationProper C orientation base Rminus Rplus
      hminus hplus F
  have hrstep := LargestParentGeometry.hrstep C orientation base Rminus Rplus hminus hplus F p hstep
  have hr1 : r 1 = p 0 := by simpa [r] using hq1
  have hr2 : r 2 = p 2 := by simpa [r] using hq2
  have hr3 : r 3 = p 3 := by simpa [r] using hq3
  let I : GaussianInt := ⟨0, 1⟩
  let w : GaussianInt := BandVectors.1 (r 3) (r 2)
  let x : GaussianInt := BandVectors.1 (r 1) (r 3)
  let y : GaussianInt := BandVectors.1 (r 2) (r 1)
  let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
  let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
  let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
  have hvsum : w + x + y = 0 := by
    simpa [w, x, y] using (VectorRecursionLaws r hr.1).1
  have hasum : wa + xa + ya = 0 := by
    simpa [wa, xa, ya] using (VectorRecursionLaws r hr.1).2.1
  have hvrec : BandVectors.1 (r 1) (r 0) = x - I * y := by
    simpa [x, y, I] using (VectorRecursionLaws r hr.1).2.2.1
  have harec : BandVectors.2 (r 1) (r 0) = xa + I * ya := by
    simpa [xa, ya, I] using (VectorRecursionLaws r hr.1).2.2.2.1
  have hvflip := LargestParentGeometry.hvflip C orientation base Rminus Rplus hminus hplus F hr
  have haflip := LargestParentGeometry.haflip C orientation base Rminus Rplus hminus hplus F hr
  rcases hselectedOcc with ⟨hUband, hUfoot, hUcent⟩
  have hUcenter := BoundaryFrameJoinGeometry.selectedCentroid C orientation base Rminus Rplus
      hminus hplus F
      D hUcent
  have hMcenter := BoundaryFrameJoinGeometry.minusCentroid C orientation base Rminus Rplus
      hminus hplus F
  have hvsumRe := BoundaryFrameJoinGeometry.firstVectorSumReal C orientation base Rminus Rplus
      hminus hplus F hvsum
  have hvsumIm := BoundaryFrameJoinGeometry.firstVectorSumImaginary C orientation base Rminus
      Rplus hminus hplus F hvsum
  have hcenterVector := LargestParentGeometry.hcenterVector C orientation base Rminus Rplus
      hminus hplus F hvrec hvflip hvsumRe hvsumIm
  have hcenterRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) hcenterVector
  have hcenterIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) hcenterVector
  have hcenter :=
    BoundaryFrameRowGeometry.centroidDifference C orientation base Rminus Rplus hminus hplus F D
      hUcenter hMcenter hcenterRe hcenterIm
  have hCcoord : C.1.1 = p 0 := F.parent.symm.trans hq1
  have hRparent : r 1 = C.1.1 := by simpa [r] using F.parent
  have hyLattice := LargestParentGeometry.hyLattice C orientation base Rminus Rplus hminus hplus
      F hr hRparent
  obtain ⟨u, huRminus, hRminusUnique⟩ :=
    RegularTileFamilyTranslationUnique base (TilingLattice C) Rminus F.minus_family
  let join : ProtoTile := TileTranslation base (u + y)
  have translate_add (T : ProtoTile) (v z : GaussianInt) :
      TileTranslation (TileTranslation T v) z = TileTranslation T (v + z) :=
          TileTranslationProperties.add T v z
  have hjoin_eq : join = TileTranslation Rminus y := by
    simpa [join, huRminus] using (translate_add base (u : GaussianInt) y).symm
  have hjoinBand := LargestParentGeometry.hjoinBand C orientation base Rminus Rplus hminus hplus F u
  have hjoinFamily := BoundaryFrameJoinGeometry.joinFamily C orientation base Rminus Rplus hminus
      hplus F hyLattice u
  have hjoinCenter := BoundaryFrameJoinGeometry.joinCentroid C orientation base Rminus Rplus hminus
      hplus F u hjoin_eq
  have hjoinCenterEq := BoundaryFrameJoinGeometry.joinCentroidEquality C orientation base Rminus
      Rplus
      hminus hplus F D hcenter u hjoinCenter
  have hUbandC := BoundaryFrameJoinGeometry.parentPrototile C orientation base Rminus Rplus
      hminus hplus F D
      hUband
  have hjoinCells := BandPrototileCentroidUnique C.1.1
    (D.tiles F.slot false) join hUbandC hjoinBand
    hjoinCenterEq
  have hjoinOdo := LargestParentGeometry.hjoinOdo C orientation base Rminus Rplus hminus hplus F
      D hCpositive hselectedOdo u hjoinBand hjoinCells
  have hjoinAncestor := BoundaryFrameJoinGeometry.joinAncestor C orientation base Rminus Rplus
      hminus hplus F D hCpositive hstrict hselectedAnc u hjoinBand hjoinCells
  have positiveCells := BandPrototileNonempty.positive
  have hUnonempty : (D.tiles F.slot false).cells.Nonempty :=
    positiveCells _ _ hCpositive hUband
  have hJnonempty : join.cells.Nonempty := by rw [← hjoinCells.1]; exact hUnonempty
  have hjoinFootEq := LargestParentGeometry.hjoinFootEq C orientation base Rminus Rplus hminus
      hplus F D u hjoinCells hUnonempty hJnonempty
  have hjoinFoot := BoundaryFrameJoinGeometry.joinFootprint C orientation base Rminus Rplus
      hminus hplus
      F D hUfoot u hjoinFootEq
  have hjoinOccurrence := BoundaryFrameJoinGeometry.joinOccurrence C orientation base Rminus Rplus
      hminus hplus F D hUcent u hjoinBand hjoinCenterEq hjoinFoot
  have hplusVector := LargestParentGeometry.hplusVector C orientation base Rminus Rplus hminus
      hplus F hvrec hvflip hvsumRe hvsumIm
  have hPcenter := BoundaryFrameJoinGeometry.plusCentroid C orientation base Rminus Rplus hminus
      hplus F
  have hPlusJoin := LargestParentGeometry.hPlusJoin C orientation base Rminus Rplus hminus hplus
      F D hUcenter u hjoinCenterEq hplusVector hPcenter
  have hSlopeInfo := LargestParentGeometry.hSlopeInfo C orientation base Rminus Rplus hminus
      hplus F D hCpositive
  rcases hSlopeInfo with ⟨rootSlope, joinSlope, hrootSlope, hjoinSlope,
    hjoinSlopeRe, hjoinSlopeIm⟩
  have hrootSlopeEq : rootSlope = F.outerSlope :=
    Option.some.inj (hrootSlope.symm.trans F.slope_outer)
  have hDoffset := LargestParentGeometry.hDoffset C orientation base Rminus Rplus hminus hplus F
      rootSlope joinSlope hjoinSlopeRe hjoinSlopeIm
  have hFminusSlope := LargestParentGeometry.hFminusSlope C orientation base Rminus Rplus hminus
      hplus F
  have hFplusSlope := LargestParentGeometry.hFplusSlope C orientation base Rminus Rplus hminus
      hplus F
  have hasumRe := BoundaryFrameJoinGeometry.secondVectorSumReal C orientation base Rminus Rplus
      hminus hplus F hasum
  have hasumIm := BoundaryFrameJoinGeometry.secondVectorSumImaginary C orientation base Rminus
      Rplus hminus hplus F hasum
  have ha10Re := LargestParentGeometry.ha10Re C orientation base Rminus Rplus hminus hplus F harec
  have ha10Im := LargestParentGeometry.ha10Im C orientation base Rminus Rplus hminus hplus F harec
  have ha01Re := LargestParentGeometry.ha01Re C orientation base Rminus Rplus hminus hplus F
      haflip ha10Im
  have ha01Im := LargestParentGeometry.ha01Im C orientation base Rminus Rplus hminus hplus F
      haflip ha10Re
  have hminusSlopeVector := LargestParentGeometry.hminusSlopeVector C orientation base Rminus
      Rplus hminus hplus F hasumRe hasumIm ha10Re ha10Im ha01Re ha01Im
  have hplusSlopeVector := LargestParentGeometry.hplusSlopeVector C orientation base Rminus Rplus
      hminus hplus F hasumRe hasumIm ha10Re ha10Im
  have toRealRe (z : GaussianInt) :
      (GaussianInt.toComplex z).re = (z.re : ℝ) :=
    (GaussianInt.intCast_re z).symm
  have toRealIm (z : GaussianInt) :
      (GaussianInt.toComplex z).im = (z.im : ℝ) :=
    (GaussianInt.intCast_im z).symm
  have ha10ReC := LargestParentGeometry.ha10ReC C orientation base Rminus Rplus hminus hplus F
      ha10Re toRealRe toRealIm
  have ha10ImC := LargestParentGeometry.ha10ImC C orientation base Rminus Rplus hminus hplus F
      ha10Im toRealRe toRealIm
  have ha01ReC := LargestParentGeometry.ha01ReC C orientation base Rminus Rplus hminus hplus F
      ha01Re toRealRe toRealIm
  have ha01ImC := LargestParentGeometry.ha01ImC C orientation base Rminus Rplus hminus hplus F
      ha01Im toRealRe toRealIm
  have hsumReC := LargestParentGeometry.hsumReC C orientation base Rminus Rplus hminus hplus F
      hasumRe toRealRe
  have hsumImC := LargestParentGeometry.hsumImC C orientation base Rminus Rplus hminus hplus F
      hasumIm toRealIm
  have hplusVectorRe := congrArg (fun z : GaussianInt => z.re) hplusSlopeVector
  have hplusVectorIm := congrArg (fun z : GaussianInt => z.im) hplusSlopeVector
  have hplusVectorRe' := LargestParentGeometry.hplusVectorRe' C orientation base Rminus Rplus
      hminus hplus F hasumRe hasumIm ha10Re ha10Im
  have hplusVectorIm' := LargestParentGeometry.hplusVectorIm' C orientation base Rminus Rplus
      hminus hplus F hasumRe hasumIm ha10Re ha10Im
  have hplusVectorReC := LargestParentGeometry.hplusVectorReC C orientation base Rminus Rplus
      hminus hplus F toRealRe toRealIm hplusVectorRe'
  have hplusVectorImC := LargestParentGeometry.hplusVectorImC C orientation base Rminus Rplus
      hminus hplus F toRealRe toRealIm hplusVectorIm'
  have hminusSlope : joinSlope - F.minusSlope = GaussianRealPoint ya :=
      LargestParentGeometry.hminusSlope C orientation base Rminus Rplus hminus hplus F rootSlope
      joinSlope hrootSlopeEq hDoffset hFminusSlope hminusSlopeVector ha10ReC ha10ImC ha01ReC
      ha01ImC hsumReC hsumImC
  have hplusSlope := LargestParentGeometry.hplusSlope C orientation base Rminus Rplus hminus
      hplus F rootSlope joinSlope hrootSlopeEq hDoffset hFplusSlope hplusSlopeVector ha10ReC
      ha10ImC ha01ReC ha01ImC hsumReC hsumImC
  have largestParentCertificate :
    Nonempty (P4458T1BoundaryPlacement F D) := LargestParentConclusion.largestParentCertificate
        C orientation base Rminus Rplus hminus hplus F D p hp hstep hq1 hq2 hq3 houter hCpositive
        hstrict hselectedAnc hselectedOdo hnegativeSlope hr hrstep hr1 hr2 hr3 hvsum hasum hvrec
        harec hvflip haflip hUband hUfoot hUcent hUcenter hMcenter hvsumRe hvsumIm hcenterVector
        hcenterRe hcenterIm hcenter hCcoord hRparent hyLattice u huRminus hRminusUnique hjoin_eq
        hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC hjoinCells hjoinOdo hjoinAncestor
        positiveCells hUnonempty hJnonempty hjoinFootEq hjoinFoot hjoinOccurrence hplusVector
        hPcenter hPlusJoin rootSlope joinSlope hrootSlope hjoinSlope hjoinSlopeRe hjoinSlopeIm
        hrootSlopeEq hDoffset hFminusSlope hFplusSlope hasumRe hasumIm ha10Re ha10Im ha01Re
        ha01Im hminusSlopeVector hplusSlopeVector ha10ReC ha10ImC ha01ReC ha01ImC hsumReC hsumImC
        hplusVectorRe hplusVectorIm hplusVectorRe' hplusVectorIm' hplusVectorReC hplusVectorImC
        hminusSlope hplusSlope
  exact largestParentCertificate


end ApollonianSuperharmonic

end
