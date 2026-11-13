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
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryPlacement
public import LeanPool.ApollonianSuperharmonic.ParentVectorsInTilingLattice
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: P4458T1SecondNewerRows]

/-!
# P4458T1SecondNewerRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SecondNewerRowsGeometry

private theorem hnegativeSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        ((0 < (F.q
            F.slot.succ).1) → (∃ s, PartialOdometerSlope (D.functions F.slot false) = some s)) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hCpositive
  rcases D.slopes F.slot false with hz | ⟨root, child, hroot, hchild, _, _⟩
  · omega
  · exact ⟨child, hchild⟩





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
        (ProperBandQuadruple r) → ((r 1 = C.1.1) → (
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        y ∈ TilingLattice C)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r hr hRparent y
  have h := (ParentVectorsInTilingLattice r hr 0 C hRparent).1
  simpa [y] using h





private theorem hjoinOdo :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), (TileOdometer (F.q F.slot.succ) (D.tiles F.slot false)
            (D.functions F.slot false)) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (BandPrototile C.1.1 join) → (((D.tiles F.slot false).cells = join.cells ∧ ((D.tiles
            F.slot false).cells = ∅ → (D.tiles F.slot false).anchor = join.anchor)) →
            (TileOdometer C.1.1 join (D.functions F.slot false)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hselectedOdo r y u join hjoinBand
      hjoinCells
  have hselectedOdo' : TileOdometer C.1.1
      (D.tiles F.slot false) (D.functions F.slot false) := by
    simpa only [← F.parent] using hselectedOdo
  exact PositiveCurvatureTileOdometerSupportTransport C.1.1
    (D.tiles F.slot false) join (D.functions F.slot false) C.2
    hselectedOdo' hjoinBand hjoinCells.1


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
  intro C orientation base Rminus Rplus hminus hplus F D r y u join hjoinCells hUnonempty
      hJoinNonemptyBase
  simp only [FootprintVertices, ite_eq_left hJoinNonemptyBase, ite_eq_left hUnonempty]
  rw [hjoinCells.1]



private theorem hq0 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q
            a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 :
            ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 :
            Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 :
            ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 :
            Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)),
            p (3 : Fin (4 : ℕ))]) → (F.q 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
            2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep
  have h := congrFun hstep 0
  simpa using h

private theorem hqA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q
            a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 :
            ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 :
            Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 :
            ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 :
            Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)),
            p (3 : Fin (4 : ℕ))]) → (F.q a.succ = p 0) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep
  have h := congrFun hstep 1
  simpa using h

private theorem hqB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q
            a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 :
            ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 :
            Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 :
            ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 :
            Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)),
            p (3 : Fin (4 : ℕ))]) → (F.q (a + 1).succ = p 2) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep
  have h := congrFun hstep 2
  simpa using h

private theorem hqD :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q
            a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 :
            ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 :
            Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 :
            ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 :
            Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)),
            p (3 : Fin (4 : ℕ))]) → (F.q (a + 2).succ = p 3) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep
  have h := congrFun hstep 3
  simpa using h

private theorem hslot :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), (Fin (4 : ℕ) → CircleCoordinates) → ((F.slot ≠ a) → (F.slot = a + 1 ∨
            F.slot = a + 2)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p selected
  have hne : F.slot.val ≠ a.val := by
    intro heq
    exact selected (Fin.ext heq)
  have hval : F.slot.val = (a.val + 1) % 3 ∨
      F.slot.val = (a.val + 2) % 3 := by omega
  rcases hval with hval | hval
  · apply Or.inl
    apply Fin.ext
    rw [Fin.val_add]
    exact hval
  · apply Or.inr
    apply Fin.ext
    rw [Fin.val_add]
    exact hval

private theorem hSlopeInfo :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        ((0 < (F.q
            F.slot.succ).1) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)];
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2);
        ∃ root child : ℝ × ℝ, PartialOdometerSlope F.odometer = some root ∧ PartialOdometerSlope
            (D.functions F.slot false) = some child ∧ child.1 - root.1 = -(1 / 2 : ℝ) * (((wa.re
            : ℤ) : ℝ) - ((wa.im : ℤ) : ℝ)) ∧ child.2 - root.2 = -(1 / 2 : ℝ) * (((wa.im : ℤ) : ℝ)
            + ((wa.re : ℤ) : ℝ)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hCpositive r wa
  rcases D.slopes F.slot false with hz | ⟨root, child, hroot, hchild, hre, him⟩
  · have hz' : (F.q F.slot.succ).1 = 0 := hz
    omega
  · refine ⟨root, child, hroot, hchild, ?_, ?_⟩
    · simpa [r, wa] using hre
    · simpa [r, wa] using him

private theorem hr2At377 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (F.q (a + 2).succ = p 3) → ((F.slot = a + (1 : Fin (3 : ℕ))) → (r 2 = p 3)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r hqD hSB
  have hidx : (a + 1) + 1 = a + 2 := by
    apply Fin.ext
    simp [Fin.val_add]
  simp only [r, hSB]
  rw [hidx]
  exact hqD

private theorem hr3At384 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (F.q a.succ = p 0) → ((F.slot = a + (1 : Fin (3 : ℕ))) → (r 3 = p 0)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r hqA hSB
  have hidx : (a + 1) + 2 = a := by
    apply Fin.ext
    simp [Fin.val_add]; omega
  simp only [r, hSB]
  rw [hidx]
  exact hqA

private theorem hparentB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (F.q (a + 1).succ = p 2) →
            ((F.slot = a + (1 : Fin (3 : ℕ))) → (p 2 = C.1.1)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hqB hSB
  calc
    p 2 = F.q (a + 1).succ := hqB.symm
    _ = F.q F.slot.succ := by rw [hSB]
    _ = C.1.1 := F.parent

private theorem houterAnc :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), (F.q a.succ = p 0) → ((0 < (F.q a.succ).1) → (AncestorOdometer (p
            0) F.outer.1.1 (D.tiles a true) F.tile (D.functions a true) F.odometer)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hAcoord hApos'
  simpa only [hAcoord] using D.ancestors a true hApos'

private theorem hvAB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple p) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        (BandVectors.1 (p 2) (p 0) = x) → (BandVectors.1 (p 0) (p 2) = I * x)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hp r I x hBA
  have h := (VectorRecursionLaws p hp.1).2.2.2.2 hp 1 |>.1
  simpa [I, hBA] using h

private theorem haAB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple p) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        (BandVectors.2 (p 2) (p 0) = xa) → (BandVectors.2 (p 0) (p 2) = -I * xa)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hp r I xa haBA
  have h := (VectorRecursionLaws p hp.1).2.2.2.2 hp 1 |>.2
  simpa [I, haBA] using h

private theorem hAoccAt427 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → ((r 1 = p 2) → ((r 2 = p 3) →
            (TileCentroid (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) •
            (GaussianRealPoint y - (-(GaussianRealPoint y).2, (GaussianRealPoint y).1)))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p r y hqB hqD hr1 hr2
  have h := (D.occurrences a true).2.2
  simpa [hqD, hqB, y, hr1, hr2] using h

private theorem hARe'At432 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → ((r 1 = p 2) → ((r 2 = p 3) → (∀
            (rootSlope : ℝ × ℝ), ∀ (aSlope : ℝ × ℝ), (aSlope.1 - rootSlope.1 = (if true = true
            then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
            ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a +
            (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → (aSlope.1 -
            rootSlope.1 = (1 / 2 : ℝ) * (ya.re - ya.im)))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r ya hqB hqD hr1 hr2 rootSlope aSlope
      hARe
  simpa [hqD, hqB, hr1, hr2, ya] using hARe

private theorem hAIm'At435 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → ((r 1 = p 2) → ((r 2 = p 3) → (∀
            (rootSlope : ℝ × ℝ), ∀ (aSlope : ℝ × ℝ), (aSlope.2 - rootSlope.2 = (if true = true
            then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
            ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a +
            (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (aSlope.2 -
            rootSlope.2 = (1 / 2 : ℝ) * (ya.im + ya.re)))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r ya hqB hqD hr1 hr2 rootSlope aSlope
      hAIm
  simpa [hqD, hqB, hr1, hr2, ya] using hAIm

private theorem hminusSlopeOffset :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (rootNeg : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (joinSlope.1 - rootNeg.1 = -(1 / 2 : ℝ) *
            ((↑wa.re : ℝ) - (↑wa.im : ℝ))) → ((joinSlope.2 - rootNeg.2 = -(1 / 2 : ℝ) * ((↑wa.im
            : ℝ) + (↑wa.re : ℝ))) → ((rootNeg = F.outerSlope) → (∀ (rootSlope : ℝ × ℝ), ∀
            (aSlope : ℝ × ℝ), (rootSlope = F.outerSlope) → ((BandVectors.2 (p 2) (p 0) = xa) →
            ((BandVectors.2 (p 0) (p 2) = -I * xa) → ((aSlope.1 - rootSlope.1 = (1 / 2 : ℝ) *
            (ya.re - ya.im)) → ((aSlope.2 - rootSlope.2 = (1 / 2 : ℝ) * (ya.im + ya.re)) →
            (((wa.re : ℝ) + (xa.re : ℝ) + (ya.re : ℝ) = 0) → (((wa.im : ℝ) + (xa.im : ℝ) + (ya.im
            : ℝ) = 0) → ((∀ (z : GaussianInt), (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀
            (z : GaussianInt), (GaussianInt.toComplex z).im = (z.im : ℝ)) → (joinSlope - aSlope =
            (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (p 2) (p 0) - BandVectors.2 (p 0) (p
            2)))))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p r I wa xa ya rootNeg joinSlope
      hjoinSlopeRe hjoinSlopeIm hrootNegEq rootSlope aSlope hrootSlopeEq haBA haAB hARe' hAIm'
      hasumReR hasumImR toRealRe toRealIm
  apply Prod.ext
  · calc
      joinSlope.1 - aSlope.1 =
          (joinSlope.1 - rootNeg.1) - (aSlope.1 - rootSlope.1) := by
            rw [hrootNegEq, hrootSlopeEq]
            ring
      _ = (1 / 2 : ℝ) * (xa.re - xa.im) := by
            rw [hjoinSlopeRe, hARe']
            linarith [hasumReR, hasumImR]
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (p 2) (p 0) - BandVectors.2 (p 0) (p 2))).1 := by
            change (1 / 2 : ℝ) * ((xa.re : ℝ) - (xa.im : ℝ)) =
              (1 / 2 : ℝ) *
                (((BandVectors.2 (p 2) (p 0) -
                  BandVectors.2 (p 0) (p 2)).re : ℤ) : ℝ)
            congr 1
            rw [haBA, haAB]
            norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
            rw [toRealRe, toRealIm]
            ring
  · calc
      joinSlope.2 - aSlope.2 =
          (joinSlope.2 - rootNeg.2) - (aSlope.2 - rootSlope.2) := by
            rw [hrootNegEq, hrootSlopeEq]
            ring
      _ = (1 / 2 : ℝ) * (xa.im + xa.re) := by
            rw [hjoinSlopeIm, hAIm']
            linarith [hasumReR, hasumImR]
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (p 2) (p 0) - BandVectors.2 (p 0) (p 2))).2 := by
            change (1 / 2 : ℝ) * ((xa.im : ℝ) + (xa.re : ℝ)) =
              (1 / 2 : ℝ) *
                (((BandVectors.2 (p 2) (p 0) -
                  BandVectors.2 (p 0) (p 2)).im : ℤ) : ℝ)
            congr 1
            rw [haBA, haAB]
            norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]

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
        ∀ (rootSlope : ℝ × ℝ), (rootSlope = F.outerSlope) → (F.plusSlope - rootSlope = (1 / 2 :
            ℝ) • GaussianRealPoint (BandVectors.2 (r 1) (r 0) + BandVectors.2 (r 0) (r 1))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootSlope hrootSlopeEq
  rw [hrootSlopeEq]
  simpa [r, GaussianRealPoint, Prod.smul_mk] using F.plus_difference

private theorem hFplusRe :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootSlope : ℝ × ℝ), (F.plusSlope - rootSlope = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.2 (r 1) (r 0) + BandVectors.2 (r 0) (r 1))) → (F.plusSlope.1 -
            rootSlope.1 = (1 / 2 : ℝ) * (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).re)
            + ((GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).re))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootSlope hFplusSlope
  have h := congrArg Prod.fst hFplusSlope
  simpa [GaussianRealPoint] using h

private theorem hFplusIm :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootSlope : ℝ × ℝ), (F.plusSlope - rootSlope = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.2 (r 1) (r 0) + BandVectors.2 (r 0) (r 1))) → (F.plusSlope.2 -
            rootSlope.2 = (1 / 2 : ℝ) * (((GaussianInt.toComplex (BandVectors.2 (r 1) (r 0))).im)
            + ((GaussianInt.toComplex (BandVectors.2 (r 0) (r 1))).im))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootSlope hFplusSlope
  have h := congrArg Prod.snd hFplusSlope
  simpa [GaussianRealPoint] using h

private theorem ha10ReAt509 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        (
        (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)];
        let I : GaussianInt := ⟨0, 1⟩;
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3);
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1);
        (BandVectors.2 (r 1) (r 0) = xa + I * ya) → ((BandVectors.2 (r 1) (r 0)).re = xa.re -
            ya.im))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa ya harec
  have h := congrArg (fun z : GaussianInt => z.re) harec
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem ha10ImAt513 :
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
  simp [I, Zsqrtd.im_mul] at h
  omega

private theorem ha01ReAt517 :
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
  simp only [Int.reduceNeg, Fin.isValue, neg_mul, Zsqrtd.re_neg, Zsqrtd.re_mul, zero_mul,
      mul_one, one_mul, zero_add, neg_neg, I] at h
  rw [ha10Im] at h
  omega

private theorem ha01ImAt522 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        (
        (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)];
        let I : GaussianInt := ⟨0, 1⟩;
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3);
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1);
        (BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0)) → (((BandVectors.2 (r 1) (r
            0)).re = xa.re - ya.im) → ((BandVectors.2 (r 0) (r 1)).im = -xa.re + ya.im)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa ya haflip ha10Re
  have h := congrArg (fun z : GaussianInt => z.im) haflip
  simp only [Int.reduceNeg, Fin.isValue, neg_mul, Zsqrtd.im_neg, Zsqrtd.im_mul, zero_mul,
      one_mul, zero_add, I] at h
  rw [ha10Re] at h
  omega

private theorem hplusReVec :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        (BandVectors.2 (p 2) (p 0) = xa) → ((BandVectors.2 (p 0) (p 2) = -I * xa) →
            ((BandVectors.2 (p 2) (p 0) + BandVectors.2 (p 0) (p 2)).re = xa.re + xa.im)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p r I xa haBA haAB
  rw [haBA, haAB]
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]

private theorem hplusImVec :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)];
        let I : GaussianInt := ⟨0, 1⟩;
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3);
        (BandVectors.2 (p 2) (p 0) = xa) → ((BandVectors.2 (p 0) (p 2) = -I * xa) →
            ((BandVectors.2 (p 2) (p 0) + BandVectors.2 (p 0) (p 2)).im = xa.im - xa.re))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p r I xa haBA haAB
  rw [haBA, haAB]
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
  omega

private theorem hFplusRe' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootSlope : ℝ × ℝ), (∀ (z : GaussianInt), (GaussianInt.toComplex z).re = (z.re : ℝ)) →
            ((F.plusSlope.1 - rootSlope.1 = (1 / 2 : ℝ) * (((GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).re) + ((GaussianInt.toComplex (BandVectors.2 (r 0) (r
            1))).re))) → (F.plusSlope.1 - rootSlope.1 = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r
            0)).re : ℝ) + ((BandVectors.2 (r 0) (r 1)).re : ℝ)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootSlope toRealRe hFplusRe
  simpa only [toRealRe] using hFplusRe

private theorem hFplusIm' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootSlope : ℝ × ℝ), (∀ (z : GaussianInt), (GaussianInt.toComplex z).im = (z.im : ℝ)) →
            ((F.plusSlope.2 - rootSlope.2 = (1 / 2 : ℝ) * (((GaussianInt.toComplex
            (BandVectors.2 (r 1) (r 0))).im) + ((GaussianInt.toComplex (BandVectors.2 (r 0) (r
            1))).im))) → (F.plusSlope.2 - rootSlope.2 = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r
            0)).im : ℝ) + ((BandVectors.2 (r 0) (r 1)).im : ℝ)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootSlope toRealIm hFplusIm
  simpa only [toRealIm] using hFplusIm

private theorem hplusSlopeOffset :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (rootSlope : ℝ × ℝ), ∀ (aSlope : ℝ × ℝ), (aSlope.1 - rootSlope.1 = (1 / 2 : ℝ) * (ya.re
            - ya.im)) → ((aSlope.2 - rootSlope.2 = (1 / 2 : ℝ) * (ya.im + ya.re)) →
            (((BandVectors.2 (r 1) (r 0)).re = xa.re - ya.im) → (((BandVectors.2 (r 1) (r 0)).im
            = xa.im + ya.re) → (((BandVectors.2 (r 0) (r 1)).re = xa.im + ya.re) →
            (((BandVectors.2 (r 0) (r 1)).im = -xa.re + ya.im) → (((BandVectors.2 (p 2) (p 0) +
            BandVectors.2 (p 0) (p 2)).re = xa.re + xa.im) → (((BandVectors.2 (p 2) (p 0) +
            BandVectors.2 (p 0) (p 2)).im = xa.im - xa.re) → ((F.plusSlope.1 - rootSlope.1 = (1
            / 2 : ℝ) * (((BandVectors.2 (r 1) (r 0)).re : ℝ) + ((BandVectors.2 (r 0) (r 1)).re :
            ℝ))) → ((F.plusSlope.2 - rootSlope.2 = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r
            0)).im : ℝ) + ((BandVectors.2 (r 0) (r 1)).im : ℝ))) → (F.plusSlope - aSlope = (1 /
            2 : ℝ) • GaussianRealPoint (BandVectors.2 (p 2) (p 0) + BandVectors.2 (p 0) (p
            2)))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p r xa ya rootSlope aSlope hARe' hAIm'
      ha10Re ha10Im ha01Re ha01Im hplusReVec hplusImVec hFplusRe' hFplusIm'
  apply Prod.ext
  · calc
      F.plusSlope.1 - aSlope.1 =
          (F.plusSlope.1 - rootSlope.1) - (aSlope.1 - rootSlope.1) := by ring
      _ = (1 / 2 : ℝ) * (xa.re + xa.im) := by
            rw [hFplusRe', hARe', ha10Re, ha01Re]
            push_cast
            ring
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (p 2) (p 0) + BandVectors.2 (p 0) (p 2))).1 := by
            change (1 / 2 : ℝ) * ((xa.re : ℝ) + (xa.im : ℝ)) =
              (1 / 2 : ℝ) *
                (((BandVectors.2 (p 2) (p 0) +
                  BandVectors.2 (p 0) (p 2)).re : ℤ) : ℝ)
            congr 1
            exact_mod_cast hplusReVec.symm
  · calc
      F.plusSlope.2 - aSlope.2 =
          (F.plusSlope.2 - rootSlope.2) - (aSlope.2 - rootSlope.2) := by ring
      _ = (1 / 2 : ℝ) * (xa.im - xa.re) := by
            rw [hFplusIm', hAIm', ha10Im, ha01Im]
            push_cast
            ring
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (p 2) (p 0) + BandVectors.2 (p 0) (p 2))).2 := by
            change (1 / 2 : ℝ) * ((xa.im : ℝ) - (xa.re : ℝ)) =
              (1 / 2 : ℝ) *
                (((BandVectors.2 (p 2) (p 0) +
                  BandVectors.2 (p 0) (p 2)).im : ℤ) : ℝ)
            congr 1
            exact_mod_cast hplusImVec.symm


private theorem hFminusSlopeAt641 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootSlope : ℝ × ℝ), (rootSlope = F.outerSlope) → (F.minusSlope - rootSlope = (1 / 2
            : ℝ) • GaussianRealPoint (BandVectors.2 (r 1) (r 0) - BandVectors.2 (r 0) (r 1))) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootSlope hrootSlopeEq
  rw [hrootSlopeEq]
  exact F.minus_difference

private theorem hFminusReAt646 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootSlope : ℝ × ℝ), (F.minusSlope - rootSlope = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.2 (r 1) (r 0) - BandVectors.2 (r 0) (r 1))) → (F.minusSlope.1 -
            rootSlope.1 = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r 0)).re : ℝ) - ((BandVectors.2
            (r 0) (r 1)).re : ℝ))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootSlope hFminusSlope
  have h := congrArg Prod.fst hFminusSlope
  simpa [GaussianRealPoint, Prod.smul_mk] using h

private theorem hFminusImAt652 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootSlope : ℝ × ℝ), (F.minusSlope - rootSlope = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.2 (r 1) (r 0) - BandVectors.2 (r 0) (r 1))) → (F.minusSlope.2 -
            rootSlope.2 = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r 0)).im : ℝ) - ((BandVectors.2
            (r 0) (r 1)).im : ℝ))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootSlope hFminusSlope
  have h := congrArg Prod.snd hFminusSlope
  simpa [GaussianRealPoint, Prod.smul_mk] using h

private theorem hdirectSlope :
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
        ∀ (joinSlope : ℝ × ℝ), ∀ (rootSlope : ℝ × ℝ), (joinSlope.2 - rootSlope.2 = -(1 / 2 : ℝ) *
            ((↑wa.im : ℝ) + (↑wa.re : ℝ))) → ((joinSlope.1 - rootSlope.1 = -(1 / 2 : ℝ) *
            ((↑wa.re : ℝ) - (↑wa.im : ℝ))) → (((↑wa.re : ℝ) + (↑xa.re : ℝ) + (↑ya.re : ℝ) = (0 :
            ℝ)) → (((↑wa.im : ℝ) + (↑xa.im : ℝ) + (↑ya.im : ℝ) = (0 : ℝ)) → ((F.minusSlope.1 -
            rootSlope.1 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 :
            ℕ)))).re : ℝ) - (↑(BandVectors.2 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ)))).re :
            ℝ))) → ((F.minusSlope.2 - rootSlope.2 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (r (1 : Fin
            (4 : ℕ))) (r (0 : Fin (4 : ℕ)))).im : ℝ) - (↑(BandVectors.2 (r (0 : Fin (4 : ℕ))) (r
            (1 : Fin (4 : ℕ)))).im : ℝ))) → ((((BandVectors.2 (r 1) (r 0)).re : ℝ) = (xa.re : ℝ)
            - (ya.im : ℝ)) → ((((BandVectors.2 (r 1) (r 0)).im : ℝ) = (xa.im : ℝ) + (ya.re : ℝ))
            → ((((BandVectors.2 (r 0) (r 1)).re : ℝ) = (xa.im : ℝ) + (ya.re : ℝ)) →
            ((((BandVectors.2 (r 0) (r 1)).im : ℝ) = -(xa.re : ℝ) + (ya.im : ℝ)) → (joinSlope -
            F.minusSlope = GaussianRealPoint ya)))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa ya joinSlope rootSlope
      hjoinSlopeIm hjoinSlopeRe hasumReR hasumImR hFminusRe hFminusIm ha10ReR ha10ImR ha01ReR
      ha01ImR
  apply Prod.ext
  · calc
      joinSlope.1 - F.minusSlope.1 =
          (joinSlope.1 - rootSlope.1) -
            (F.minusSlope.1 - rootSlope.1) := by ring
      _ = (ya.re : ℝ) := by
        rw [hjoinSlopeRe, hFminusRe,
          ha10ReR, ha01ReR]
        linarith [hasumReR, hasumImR]
  · calc
      joinSlope.2 - F.minusSlope.2 =
          (joinSlope.2 - rootSlope.2) -
            (F.minusSlope.2 - rootSlope.2) := by ring
      _ = (ya.im : ℝ) := by
        rw [hjoinSlopeIm, hFminusIm,
          ha10ImR, ha01ImR]
        linarith [hasumReR, hasumImR]

private theorem hleftCent :
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
        (TileCentroid (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y) → (∀ (u
            : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileCentroid (D.tiles F.slot false) = TileCentroid join) → (TileCentroid join -
            TileCentroid Rminus = GaussianRealPoint y)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r y hcenter u join hjoinCenterEq
  rw [← hjoinCenterEq]
  exact hcenter

private theorem hbaseT :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer),
            (P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus) → (∀ (t : Fin
            (4 : ℕ) → CircleCoordinates), (t 0 = C.1.1) → (BandPrototile (t 0) base)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F t htC
  rw [htC]
  exact F.base_band

private theorem hleftTouch :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple t) → ((t (0 : Fin (4 : ℕ)) = p (2 : Fin (4 : ℕ))) → ((t (1 : Fin
            (4 : ℕ)) = p (3 : Fin (4 : ℕ))) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (join ∈ RegularTileFamily base (TilingLattice C)) → ((r 1 = p 2) → ((r 2 = p 3) →
            ((TileCentroid join - TileCentroid Rminus = GaussianRealPoint y) → ((t 0 = C.1.1) →
            ((BandPrototile (t 0) base) → (TileTouching Rminus join))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p t ht ht0 ht1 r y u join hjoinFamily hr1
      hr2 hleftCent htC hbaseT
  apply (BandRegularTileTouchingClassification C t ht htC
    base hbaseT Rminus join F.minus_family hjoinFamily).2
  exact ⟨0, Or.inl (by simpa [y, ht0, ht1, hr1, hr2] using hleftCent)⟩

private theorem hleftAdjacent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4
            : ℕ) → CircleCoordinates), (ProperBandQuadruple t) → ((t (0 : Fin (4 : ℕ)) = p (2 :
            Fin (4 : ℕ))) → ((t (1 : Fin (4 : ℕ)) = p (3 : Fin (4 : ℕ))) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileOdometer C.1.1 join (D.functions F.slot false)) → (∀ (joinSlope : ℝ × ℝ),
            (PartialOdometerSlope (D.functions F.slot false) = some joinSlope) → ((r 1 = p 2) →
            ((r 2 = p 3) → ((joinSlope - F.minusSlope = GaussianRealPoint ya) → ((TileCentroid
            join - TileCentroid Rminus = GaussianRealPoint y) → ((t 0 = C.1.1) →
            (LeftLatticeAdjacent C Rminus join hminus (D.functions F.slot false))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D p t ht ht0 ht1 r y ya u join hjoinOdo
      joinSlope hjoinSlope hr1 hr2 hdirectSlope hleftCent htC
  refine ⟨F.minus_odo, hjoinOdo, F.minusSlope, joinSlope,
    F.slope_minus, hjoinSlope, ?_⟩
  right
  refine ⟨t, 0, true, ht, htC, ?_, ?_, ?_⟩
  · simpa [y, ht0, ht1, hr1, hr2] using hleftCent
  · have h := congrArg Prod.fst hdirectSlope
    simpa [GaussianRealPoint, ya, ht0, ht1, hr1, hr2] using h
  · have h := congrArg Prod.snd hdirectSlope
    simpa [GaussianRealPoint, ya, ht0, ht1, hr1, hr2] using h

private theorem hMnonempty :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer),
            (P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus) → ((∀ (c :
            CircleCoordinates), ∀ (T : ProtoTile), 0 < c.1 → BandPrototile c T →
            T.cells.Nonempty) → (Rminus.cells.Nonempty)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F positiveCells
  apply positiveCells C.1.1 Rminus C.2
  exact TileOdometerBandPrototile C.1.1 Rminus hminus F.minus_odo

private theorem hJnonempty :
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
            (join.cells.Nonempty)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r y u join hjoinCells hUnonempty
  rw [← hjoinCells.1]
  exact hUnonempty

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
  have htch := hleftTouch
  rw [← heq] at htch
  rcases htch with h | h | h
  · exact hMnonempty.ne_empty ((Finset.disjoint_self_iff_empty _).mp h.2.2.1)
  · exact hMnonempty.ne_empty h.1
  · exact hMnonempty.ne_empty h.1

private theorem hnonunit :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer),
            (P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus) → ((Fin (3 :
            ℕ)) → ((Fin (4 : ℕ) → CircleCoordinates) → (∀ (t : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple t) → ((t 0 = C.1.1) → (C.1.1.1 ≠ 1))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p t ht htC
  have hcurv := ProperBandCurvatureStructure t ht
  have hrootlarge : 1 < (t 0).1 := by
    by_contra hn
    have hrootle : (t 0).1 ≤ 1 := by omega
    have hzeros : ∀ k : Fin 3, (t k.succ).1 = 0 := by
      intro k
      have hnonneg := hcurv.2.1 k
      have hbelow := ht.2 k
      omega
    exact ((by decide : (0 : Fin 3) ≠ 1)
      (hcurv.2.2 0 1 (hzeros 0) (hzeros 1))).elim
  have hcurvEq : (t 0).1 = C.1.1.1 := congrArg Prod.fst htC
  rw [← hcurvEq]
  exact ne_of_gt hrootlarge

private theorem leftString :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (hp : ProperBandQuadruple p), (![F.q (0 : Fin (4 :
            ℕ)), F.q a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ]
            = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ)
            * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin
            (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3
            : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 :
            ℕ)), p (3 : Fin (4 : ℕ))]) → (∀ (hB : F.slot = a + (1 : Fin (3 : ℕ)) → C.1.1.1 = (1 :
            ℤ) → UnitOccurrenceOrientation p (1 : Fin (3 : ℕ)) orientation), (F.slot = a +
            (2 : Fin (3 : ℕ)) → C.1.1.1 = (1 : ℤ) → UnitOccurrenceOrientation p (2 : Fin (3 : ℕ))
            orientation) → ((F.slot ≠ a) → (∀ (t : Fin (4 : ℕ) → CircleCoordinates), (F.slot = a
                + (2 : Fin (3 : ℕ)) → C.1.1.1 = (1 : ℤ) →
            UnitOccurrenceOrientation t (0 : Fin (3 : ℕ)) orientation) → ((0 < (F.q
            F.slot.succ).1) → (((F.q F.slot.succ).1 < (F.q 0).1) → ((AncestorOdometer (F.q
                F.slot.succ) F.outer.1.1 (D.tiles F.slot false) F.tile
                (D.functions F.slot false)
            F.odometer) → ((TileOdometer (F.q F.slot.succ) (D.tiles F.slot false)
            (D.functions F.slot false)) → ((∃ s, PartialOdometerSlope
            (D.functions F.slot false) = some s) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → ((r 1 = C.1.1) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (w + x + y = 0) → ((wa + xa + ya = 0) → (∀ (hvrec : BandVectors.1 (r 1)
            (r 0) = x - I * y), (BandVectors.2 (r 1) (r 0) = xa + I * ya) → (∀ (hvflip :
                BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0)), (BandVectors.2
            (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0)) → ((w.re + x.re + y.re = 0) → ((w.im +
                x.im + y.im = 0) → ((BandPrototile (F.q F.slot.succ)
            (D.tiles F.slot false)) → ((FootprintVertices (D.tiles F.slot false) ⊆
            FootprintVertices F.tile) → ((TileCentroid (D.tiles F.slot false) -
            TileCentroid F.tile = (if false = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) → ((TileCentroid (D.tiles F.slot
            false) - TileCentroid F.tile = -(1 / 2 : ℝ) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) → (∀ (hMcenter : TileCentroid
            Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (r 1)
            (r 0) - BandVectors.1 (r 0) (r 1))), (-w + I * w - BandVectors.1 (r
            1) (r 0) + BandVectors.1 (r 0) (r 1) = 2 * y) → (((↑(-w + I * w -
            BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin
            (4 : ℕ))) (r (1 : Fin (4 : ℕ)))).re : ℝ) = (↑((2 : GaussianInt) * y).re : ℝ)) →
                (((↑(-w + I * w - BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 :
            ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ)))).im : ℝ) = (↑((2 :
            GaussianInt) * y).im : ℝ)) → (∀ (hcenter : TileCentroid (D.tiles F.slot false) -
            TileCentroid Rminus = GaussianRealPoint y), (y ∈ TilingLattice C) → (∀ (u :
                ↥(TilingLattice C)), (Rminus = TileTranslation base (↑u : GaussianInt)) → (
        let join : ProtoTile := TileTranslation base (u + y)
        (join = TileTranslation Rminus y) → ((BandPrototile C.1.1 join) → (∀ (hjoinFamily : join
            ∈ RegularTileFamily base (TilingLattice C)), (TileCentroid join = TileCentroid Rminus
            + GaussianRealPoint y) → (∀ (hjoinCenterEq : TileCentroid (D.tiles F.slot false) =
            TileCentroid join), (BandPrototile
            C.1.1 (D.tiles F.slot false)) → (((D.tiles F.slot false).cells =
            join.cells ∧ ((D.tiles F.slot false).cells = ∅ → (D.tiles F.slot false).anchor =
            join.anchor)) → (∀ (hjoinOdo : TileOdometer C.1.1 join (D.functions F.slot false)),
                (AncestorOdometer C.1.1 F.outer.1.1 join F.tile (D.functions F.slot
            false) F.odometer) → (((D.tiles F.slot false).cells.Nonempty) →
                ((join.cells.Nonempty) → ((FootprintVertices join =
            FootprintVertices (D.tiles F.slot false)) → ((FootprintVertices join ⊆
            FootprintVertices F.tile) → ((BandSubtileOccurrence F.q F.tile
            F.slot false join) → ((F.q 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p
            1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2)) → ((F.q a.succ = p
            0) → ((F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → (∀ (rootNeg : ℝ × ℝ), ∀
                (joinSlope : ℝ × ℝ), (PartialOdometerSlope F.odometer = some
            rootNeg) → (∀ (hjoinSlope : PartialOdometerSlope (D.functions F.slot false) = some
            joinSlope), (rootNeg = F.outerSlope) → (∀ (hSB : F.slot = a + (1 : Fin
            (3 : ℕ))), (r 1 = p 2) → ((r 2 = p 3) → ((r 3 = p 0) → ((F.q a.succ = p 0) → ((0 <
                (F.q a.succ).1) → (∀ (rootSlope : ℝ × ℝ), (joinSlope.2 - rootSlope.2 = -(1 / 2 :
                ℝ) * ((↑wa.im : ℝ) + (↑wa.re :
            ℝ))) → ((joinSlope.1 - rootSlope.1 = -(1 / 2 : ℝ) * ((↑wa.re : ℝ) -
            (↑wa.im : ℝ))) → (∀ (aSlope : ℝ × ℝ), (PartialOdometerSlope F.odometer =
            some rootSlope) → (∀ (haSlope : PartialOdometerSlope (D.functions a true) = some
            aSlope), (aSlope.1 - rootSlope.1 = (if true = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1
            : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ)
            (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((aSlope.2 - rootSlope.2 = (if
            true = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a +
            (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 :
            ℕ))).succ)).re : ℝ))) → ((rootSlope = F.outerSlope) → (
        let outerA : BandCircle :=
          ⟨⟨p 0, ⟨Or.inl (ProperBandCurvatureStructure p hp).1,
            ⟨p, hp.1, 0, rfl⟩⟩⟩, (ProperBandCurvatureStructure p hp).1⟩
        (outerA.1.1 = F.q a.succ) → (∀ (hparentB : p (2 : Fin (4 :
            ℕ)) = C.1.1), ∀ (houterOdo : TileOdometer (p (0 : Fin (4 : ℕ))) (D.tiles a true)
            (D.functions a true)), ∀ (houterBand : BandPrototile (p (0 : Fin (4 : ℕ))) (D.tiles a
            true)), (AncestorOdometer (p (0 : Fin (4 : ℕ))) F.outer.1.1 (D.tiles a
                true) F.tile (D.functions a true)
            F.odometer) → (∀ (hBA : BandVectors.1 (p (2 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) =
                x), (BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) = xa) → (∀ (hvAB :
                BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ))) = I * x),
                (BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ))) = -I * xa) → (∀ (hidx2
                : Fin.succ (1 : Fin (3 : ℕ)) = (2 : Fin ((3 : ℕ) + (1 : ℕ)))), ∀ (hAocc :
                TileCentroid
            (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • (GaussianRealPoint y -
            (-(GaussianRealPoint y).2, (GaussianRealPoint y).1))), (aSlope.1 -
            rootSlope.1 = (1 / 2 : ℝ) * ((↑ya.re : ℝ) - (↑ya.im : ℝ))) → ((aSlope.2 -
            rootSlope.2 = (1 / 2 : ℝ) * ((↑ya.im : ℝ) + (↑ya.re : ℝ))) → ((wa.re +
            xa.re + ya.re = (0 : ℤ)) → ((wa.im + xa.im + ya.im = (0 : ℤ)) → (((↑wa.re : ℝ) +
                (↑xa.re : ℝ) + (↑ya.re : ℝ) = (0 : ℝ)) → (((↑wa.im : ℝ) +
            (↑xa.im : ℝ) + (↑ya.im : ℝ) = (0 : ℝ)) → (∀ (hminusSlopeOffset : joinSlope - aSlope =
            (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (0 : Fin (4 :
            ℕ))) - BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ))))), (F.plusSlope -
                rootSlope = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (r (1 : Fin
            (4 : ℕ))) (r (0 : Fin (4 : ℕ))) + BandVectors.2 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4
            : ℕ))))) → ((F.plusSlope.1 - rootSlope.1 = (1 / 2 : ℝ) *
            (((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (r (1 : Fin (4 : ℕ))) (r
            (0 : Fin (4 : ℕ))))).re + ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2
            (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))))).re)) → ((F.plusSlope.2 -
            rootSlope.2 = (1 / 2 : ℝ) * (((GaussianInt.toComplex : GaussianInt → ℂ)
            (BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))))).im +
            ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (r (0 : Fin (4 : ℕ))) (r (1
            : Fin (4 : ℕ))))).im)) → (((BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (0 : Fin
            (4 : ℕ)))).re = xa.re - ya.im) → (((BandVectors.2 (r (1 : Fin (4 : ℕ))) (r
            (0 : Fin (4 : ℕ)))).im = xa.im + ya.re) → (((BandVectors.2 (r (0 : Fin (4 :
            ℕ))) (r (1 : Fin (4 : ℕ)))).re = xa.im + ya.re) → (((BandVectors.2 (r (0 :
            Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ)))).im = -xa.re + ya.im) → (((BandVectors.2 (p (2 :
                Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) + BandVectors.2 (p (0 :
            Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ)))).re = xa.re + xa.im) → (((BandVectors.2 (p (2 :
                Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) + BandVectors.2 (p (0 :
            Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ)))).im = xa.im - xa.re) → ((F.plusSlope.1 -
                rootSlope.1 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (r (1 : Fin (4 : ℕ)))
            (r (0 : Fin (4 : ℕ)))).re : ℝ) + (↑(BandVectors.2 (r (0 : Fin (4 : ℕ))) (r (1 : Fin
            (4 : ℕ)))).re : ℝ))) → ((F.plusSlope.2 - rootSlope.2 = (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ)))).im : ℝ) +
            (↑(BandVectors.2 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ)))).im : ℝ))) → (∀
                (hplusSlopeOffset : F.plusSlope - aSlope = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) + BandVectors.2 (p (0 :
            Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ))))),
        let G : P4458T1BoundaryFrame C orientation base join Rplus
            (D.functions F.slot false) hplus := {
          outer := outerA
          q := p
          proper := hp
          slot := 1
          child := rfl
          parent := hparentB
          tile := D.tiles a true
          odometer := D.functions a true
          outer_odo := houterOdo
          minus_odo := hjoinOdo
          plus_odo := F.plus_odo
          outer_band := houterBand
          base_band := F.base_band
          minus_family := hjoinFamily
          plus_family := F.plus_family
          chart := by
            intro hunit
            exact hB hSB (by simpa only [hparentB] using hunit)
          minus_centroid := by
            rw [hidx2]
            rw [show TileCentroid join - TileCentroid (D.tiles a true) =
              (TileCentroid join - TileCentroid Rminus) +
                (TileCentroid Rminus - TileCentroid F.tile) -
                (TileCentroid (D.tiles a true) - TileCentroid F.tile) by
                  ext <;> dsimp <;> ring]
            rw [← hjoinCenterEq, hcenter, hMcenter, hAocc,
              hvflip, hvrec, hBA, hvAB]
            apply Prod.ext <;>
              simp [GaussianRealPoint, I, Prod.smul_mk,
                Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
          plus_centroid := by
            rw [hidx2]
            rw [show TileCentroid Rplus - TileCentroid (D.tiles a true) =
              (TileCentroid Rplus - TileCentroid F.tile) -
                (TileCentroid (D.tiles a true) - TileCentroid F.tile) by
                  ext <;> dsimp <;> ring]
            have hPcenter : TileCentroid Rplus - TileCentroid F.tile =
                (1 / 2 : ℝ) • GaussianRealPoint
                  (BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1)) := by
              simpa [r] using F.plus_centroid
            rw [hPcenter, hAocc, hvflip, hvrec, hBA, hvAB]
            apply Prod.ext <;>
              simp [GaussianRealPoint, I, Prod.smul_mk,
                Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
          outerSlope := aSlope
          minusSlope := joinSlope
          plusSlope := F.plusSlope
          slope_outer := haSlope
          slope_minus := hjoinSlope
          slope_plus := F.slope_plus
          minus_difference := hminusSlopeOffset
          plus_difference := hplusSlopeOffset
        }
        (G.outer.1.1 = F.q a.succ) →
            ((P4458T1BoundarySide F join Rplus (D.functions F.slot false) hplus) →
            ((F.minusSlope - rootSlope = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (r (1 :
            Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) - BandVectors.2 (r (0 : Fin (4 : ℕ))) (r (1 : Fin
            (4 : ℕ))))) → ((F.minusSlope.1 - rootSlope.1 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (r (1
            : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ)))).re : ℝ) - (↑(BandVectors.2 (r (0 : Fin (4 :
            ℕ))) (r (1 : Fin (4 : ℕ)))).re : ℝ))) → ((F.minusSlope.2 - rootSlope.2 = (1 / 2 : ℝ)
            * ((↑(BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ)))).im : ℝ) -
            (↑(BandVectors.2 (r (0 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ)))).im : ℝ))) →
            ((((BandVectors.2 (r 1) (r 0)).re : ℝ) = (xa.re : ℝ) - (ya.im : ℝ)) →
            ((((BandVectors.2 (r 1) (r 0)).im : ℝ) = (xa.im : ℝ) + (ya.re : ℝ)) →
            ((((BandVectors.2 (r 0) (r 1)).re : ℝ) = (xa.im : ℝ) + (ya.re : ℝ)) →
            ((((BandVectors.2 (r 0) (r 1)).im : ℝ) = -(xa.re : ℝ) + (ya.im : ℝ)) → ((joinSlope -
            F.minusSlope = GaussianRealPoint ya) → ((TileCentroid join - TileCentroid Rminus =
            GaussianRealPoint y) → ((TileTouching Rminus join) → ((LeftLatticeAdjacent C Rminus
            join hminus (D.functions F.slot false)) → ((Rminus.cells.Nonempty) →
            ((join.cells.Nonempty) → ((Rminus ≠ join) → ((C.1.1.1 ≠ 1) → (TileString C
            orientation base Rminus join [Rminus,
                join])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                )))))))))))))))))))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hp hstep hB hD selected t olderChart
      hCpositive hstrict hselectedAnc hselectedOdo hnegativeSlope r hr hRparent I w x y wa xa ya
      hvsum hasum hvrec harec hvflip haflip hvsumRe hvsumIm hUband hUfoot hUcent hUcenter
      hMcenter hcenterVector hcenterRe hcenterIm hcenter hyLattice u huRminus join hjoin_eq
      hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC hjoinCells hjoinOdo hjoinAncestor
      hUnonempty hJoinNonemptyBase hjoinFootEq hjoinFoot hjoinOccurrence hq0 hqA hqB hqD rootNeg
      joinSlope hrootNeg hjoinSlope hrootNegEq hSB hr1 hr2 hr3 hAcoord hApos' rootSlope
      hjoinSlopeIm hjoinSlopeRe aSlope hrootSlope haSlope hARe hAIm hrootSlopeEq outerA hparentA
      hparentB houterOdo houterBand houterAnc hBA haBA hvAB haAB hidx2 hAocc hARe' hAIm' hasumRe
      hasumIm hasumReR hasumImR hminusSlopeOffset hFplusSlope hFplusRe hFplusIm ha10Re ha10Im
      ha01Re ha01Im hplusReVec hplusImVec hFplusRe' hFplusIm' hplusSlopeOffset G houterEq hright
      hFminusSlope hFminusRe hFminusIm ha10ReR ha10ImR ha01ReR ha01ImR hdirectSlope hleftCent
      hleftTouch hleftAdjacent hMnonempty hJnonempty hleftNe hnonunit
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
    have hp' : 1 ≤ pre.length := by
      cases pre with
      | nil => simp at hpre
      | cons x xs => simp
    have hq' : 1 ≤ post.length := by
      cases post with
      | nil => simp at hpost
      | cons x xs => simp
    simp at hlen
    omega

private theorem hr2At770 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (F.q a.succ = p 0) → ((F.slot = a + (2 : Fin (3 : ℕ))) → (r 2 = p 0)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r hqA hSD
  have hidx : (a + 2) + 1 = a := by
    apply Fin.ext
    simp [Fin.val_add]; omega
  simp only [r, hSD]
  rw [hidx]
  exact hqA

private theorem hr3At777 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (F.q (a + 1).succ = p 2) → ((F.slot = a + (2 : Fin (3 : ℕ))) → (r 3 = p 2)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r hqB hSD
  have hidx : (a + 2) + 2 = a + 1 := by
    apply Fin.ext
    simp [Fin.val_add]; omega
  simp only [r, hSD]
  rw [hidx]
  exact hqB

private theorem hBpos :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple t) → ((t (0 : Fin (4 : ℕ)) = p (2 : Fin (4 : ℕ))) → (0 < (p
            2).1)) ) := by
  classical
  intro p t ht ht0
  have hcurv := ProperBandCurvatureStructure t ht
  simpa [ht0] using hcurv.1

private theorem houterAOdo :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), (F.q a.succ = p 0) → (TileOdometer (p 0) (D.tiles a true)
            (D.functions a true)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hqA
  simpa only [hqA] using D.odometers a true

private theorem houterAAnc :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), (F.q a.succ = p 0) → ((0 < (p 0).1) → (AncestorOdometer (p 0)
            F.outer.1.1 (D.tiles a true) F.tile (D.functions a true) F.odometer)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hqA hApos
  simpa only [hqA] using D.ancestors a true (by rw [hqA]; exact hApos)

private theorem hparentD :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (F.q (a + 2).succ = p 3) →
            ((F.slot = a + (2 : Fin (3 : ℕ))) → (p 3 = C.1.1)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hqD hSD
  rw [← hqD, ← hSD]
  exact F.parent

private theorem hAoccAt816 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        (F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → ((r 1 = p 3) → ((r 3 = p 2) →
            (TileCentroid (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) •
            (GaussianRealPoint x - (-(GaussianRealPoint x).2, (GaussianRealPoint x).1)))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p r x hqB hqD hr1 hr3
  have h := (D.occurrences a true).2.2
  simpa [hqD, hqB, x, hr1, hr3] using h

private theorem hpRot :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple p) → (
        let pRot : Fin 4 → CircleCoordinates := ![p 0, p 3, p 1, p 2]
        ProperBandQuadruple pRot) ) := by
  classical
  intro p hp pRot
  refine ⟨SemiProperQuadruple.rotate
    (SemiProperQuadruple.rotate hp.1), ?_⟩
  intro j
  fin_cases j
  · simpa [pRot] using hp.2 2
  · simpa [pRot] using hp.2 0
  · simpa [pRot] using hp.2 1

private theorem hRotV :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let pRot : Fin 4 → CircleCoordinates := ![p 0, p 3, p 1, p 2]
        (ProperBandQuadruple pRot) → (BandVectors.1 (p 0) (p 3) = I * BandVectors.1 (p 3) (p 0))
            ) := by
  classical
  intro p I pRot hpRot
  have h := (VectorRecursionLaws pRot hpRot.1).2.2.2.2 hpRot 0 |>.1
  simpa [pRot, I] using h

private theorem hRotA :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        let pRot : Fin 4 → CircleCoordinates := ![p 0, p 3, p 1, p 2]
        (ProperBandQuadruple pRot) → (BandVectors.2 (p 0) (p 3) = -I * BandVectors.2 (p 3) (p 0))
            ) := by
  classical
  intro p I pRot hpRot
  have h := (VectorRecursionLaws pRot hpRot.1).2.2.2.2 hpRot 0 |>.2
  simpa [pRot, I] using h

private theorem hRotVRe :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.1 (p 0) (p 3) = I * BandVectors.1 (p 3) (p 0)) → ((BandVectors.1 (p 0) (p
            3)).re = -(BandVectors.1 (p 3) (p 0)).im) ) := by
  classical
  intro p I hRotV
  have h := congrArg (fun z : GaussianInt => z.re) hRotV
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hRotVIm :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.1 (p 0) (p 3) = I * BandVectors.1 (p 3) (p 0)) → ((BandVectors.1 (p 0) (p
            3)).im = (BandVectors.1 (p 3) (p 0)).re) ) := by
  classical
  intro p I hRotV
  have h := congrArg (fun z : GaussianInt => z.im) hRotV
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hrecVRe :
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
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 1) (r 0)).re = x.re + y.im)
            ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I x y hvrec
  have h := congrArg (fun z : GaussianInt => z.re) hvrec
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hrecVIm :
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
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 1) (r 0)).im = x.im - y.re)
            ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I x y hvrec
  have h := congrArg (fun z : GaussianInt => z.im) hvrec
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hflipVRe :
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
        (BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0)) → ((BandVectors.1 (r 0) (r
            1)).re = -(BandVectors.1 (r 1) (r 0)).im) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I hvflip
  have h := congrArg (fun z : GaussianInt => z.re) hvflip
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hflipVIm :
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
        (BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0)) → ((BandVectors.1 (r 0) (r
            1)).im = (BandVectors.1 (r 1) (r 0)).re) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I hvflip
  have h := congrArg (fun z : GaussianInt => z.im) hvflip
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hrecVC :
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
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (BandVectors.1 (r 1) (r 0) = x - I * y) → (GaussianInt.toComplex (BandVectors.1 (r 1) (r
            0)) = GaussianInt.toComplex x - GaussianInt.toComplex I * GaussianInt.toComplex y) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I x y hvrec
  have h := congrArg GaussianInt.toComplex hvrec
  simpa only [GaussianInt.toComplex_sub, GaussianInt.toComplex_mul] using h

private theorem hflipVC :
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
        (BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0)) → (GaussianInt.toComplex
            (BandVectors.1 (r 0) (r 1)) = GaussianInt.toComplex I * GaussianInt.toComplex
            (BandVectors.1 (r 1) (r 0))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I hvflip
  have h := congrArg GaussianInt.toComplex hvflip
  simpa only [GaussianInt.toComplex_mul] using h

private theorem hRotVC :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.1 (p 0) (p 3) = I * BandVectors.1 (p 3) (p 0)) → (GaussianInt.toComplex
            (BandVectors.1 (p 0) (p 3)) = GaussianInt.toComplex I * GaussianInt.toComplex
            (BandVectors.1 (p 3) (p 0))) ) := by
  classical
  intro p I hRotV
  have h := congrArg GaussianInt.toComplex hRotV
  simpa only [GaussianInt.toComplex_mul] using h

private theorem hleftAminus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) → ((TileCentroid (D.tiles a
            true) - TileCentroid F.tile = (1 / 2 : ℝ) • (GaussianRealPoint x -
            (-(GaussianRealPoint x).2, (GaussianRealPoint x).1))) → ((((BandVectors.1 (p 0) (p
            3)).re : ℝ) = -((BandVectors.1 (p 3) (p 0)).im : ℝ)) → ((((BandVectors.1 (p 0) (p
            3)).im : ℝ) = ((BandVectors.1 (p 3) (p 0)).re : ℝ)) → ((((BandVectors.1 (r 1) (r
            0)).re : ℝ) = (x.re : ℝ) + (y.im : ℝ)) → ((((BandVectors.1 (r 1) (r 0)).im : ℝ) =
            (x.im : ℝ) - (y.re : ℝ)) → ((((BandVectors.1 (r 0) (r 1)).re : ℝ) = -((BandVectors.1
            (r 1) (r 0)).im : ℝ)) → ((((BandVectors.1 (r 0) (r 1)).im : ℝ) = ((BandVectors.1 (r
            1) (r 0)).re : ℝ)) → ((y = BandVectors.1 (p 0) (p 3)) → (TileCentroid Rminus -
            TileCentroid (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (p 3)
            (p 0) - BandVectors.1 (p 0) (p 3))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p r x y hMcenter hAocc hRotVReR
      hRotVImR hrecVReR hrecVImR hflipVReR hflipVImR hyRot
  rw [show TileCentroid Rminus - TileCentroid (D.tiles a true) =
    (TileCentroid Rminus - TileCentroid F.tile) -
      (TileCentroid (D.tiles a true) - TileCentroid F.tile) by
        ext <;> dsimp <;> ring]
  rw [hMcenter, hAocc]
  apply Prod.ext
  · simp only [GaussianRealPoint, Prod.smul_mk, Zsqrtd.re_sub,
      Zsqrtd.im_sub,
      Int.cast_sub]
    rw [hRotVReR, hflipVReR, hflipVImR,
      hrecVReR, hrecVImR]
    rw [hyRot]
    rw [hRotVReR, hRotVImR]
    simp only [Prod.fst_sub]
    rw [Prod.smul_fst]
    simp only [Prod.fst_sub]
    ring
  · simp only [GaussianRealPoint, Prod.smul_mk, Zsqrtd.re_sub,
      Zsqrtd.im_sub,
      Int.cast_sub]
    rw [hRotVImR, hflipVReR, hflipVImR,
      hrecVReR, hrecVImR]
    rw [hyRot]
    rw [hRotVReR, hRotVImR]
    simp only [Prod.snd_sub]
    rw [Prod.smul_snd]
    simp only [Prod.snd_sub]
    ring

private theorem hleftAplus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (TileCentroid (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y) → (∀ (u
            : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileCentroid (D.tiles F.slot false) = TileCentroid join) → ((r 1 = p 3) → ((r 2 = p 0) →
            ((TileCentroid Rminus - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.1 (p 3) (p 0) - BandVectors.1 (p 0) (p 3))) →
            (TileCentroid join - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (p 3) (p 0) + BandVectors.1 (p 0) (p 3))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p r y hcenter u join hjoinCenterEq hr1
      hr2 hleftAminus
  rw [show TileCentroid join - TileCentroid (D.tiles a true) =
    (TileCentroid join - TileCentroid Rminus) +
      (TileCentroid Rminus - TileCentroid (D.tiles a true)) by
        ext <;> dsimp <;> ring]
  rw [show TileCentroid join - TileCentroid Rminus = GaussianRealPoint y by
    rw [← hjoinCenterEq]
    exact hcenter, hleftAminus]
  apply Prod.ext <;> simp [GaussianRealPoint, y, hr1, hr2] <;> ring

private theorem hARe'At945 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        (F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → ((r 1 = p 3) → ((r 3 = p 2) → (∀
            (rootA : ℝ × ℝ), ∀ (slopeA : ℝ × ℝ), (slopeA.1 - rootA.1 = (if true = true then (1 :
            ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
            ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a +
            (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → (slopeA.1 -
            rootA.1 = (1 / 2 : ℝ) * ((xa.re : ℝ) - (xa.im : ℝ))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r xa hqB hqD hr1 hr3 rootA slopeA hARe
  simpa [hqD, hqB, hr1, hr3, xa] using hARe

private theorem hAIm'At948 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        (F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → ((r 1 = p 3) → ((r 3 = p 2) → (∀
            (rootA : ℝ × ℝ), ∀ (slopeA : ℝ × ℝ), (slopeA.2 - rootA.2 = (if true = true then (1 :
            ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
            ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a +
            (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (slopeA.2 -
            rootA.2 = (1 / 2 : ℝ) * ((xa.im : ℝ) + (xa.re : ℝ))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r xa hqB hqD hr1 hr3 rootA slopeA hAIm
  simpa [hqD, hqB, hr1, hr3, xa] using hAIm

private theorem ha10ImAt955 :
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
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem ha01ReAt959 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        (
        (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)];
        let I : GaussianInt := ⟨0, 1⟩;
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3);
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1);
        (BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0)) → (((BandVectors.2 (r 1) (r
            0)).im = xa.im + ya.re) → ((BandVectors.2 (r 0) (r 1)).re = xa.im + ya.re)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa ya haflip ha10Im
  have h := congrArg (fun z : GaussianInt => z.re) haflip
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem ha01ImAt963 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        (
        (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)];
        let I : GaussianInt := ⟨0, 1⟩;
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3);
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1);
        (BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0)) → (((BandVectors.2 (r 1) (r
            0)).re = xa.re - ya.im) → ((BandVectors.2 (r 0) (r 1)).im = -xa.re + ya.im)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r I xa ya haflip ha10Re
  have h := congrArg (fun z : GaussianInt => z.im) haflip
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hRotARe :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.2 (p 0) (p 3) = -I * BandVectors.2 (p 3) (p 0)) → ((BandVectors.2 (p 0) (p
            3)).re = (BandVectors.2 (p 3) (p 0)).im) ) := by
  classical
  intro p I hRotA
  have h := congrArg (fun z : GaussianInt => z.re) hRotA
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hRotAIm :
    (by
      classical
      exact
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.2 (p 0) (p 3) = -I * BandVectors.2 (p 3) (p 0)) → ((BandVectors.2 (p 0) (p
            3)).im = -(BandVectors.2 (p 3) (p 0)).re) ) := by
  classical
  intro p I hRotA
  have h := congrArg (fun z : GaussianInt => z.im) hRotA
  norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  omega

private theorem hFminusSlopeAt991 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootA : ℝ × ℝ), (rootA = F.outerSlope) → (F.minusSlope - rootA = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.2 (r 1) (r 0) - BandVectors.2 (r 0) (r 1))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootA hrootAEq
  rw [hrootAEq]
  exact F.minus_difference

private theorem hFminusReAt996 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootA : ℝ × ℝ), (F.minusSlope - rootA = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.2 (r 1) (r 0) - BandVectors.2 (r 0) (r 1))) → (F.minusSlope.1 - rootA.1
            = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r 0)).re : ℝ) - ((BandVectors.2 (r 0) (r
            1)).re : ℝ))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootA hFminusSlope
  have h := congrArg Prod.fst hFminusSlope
  simpa [GaussianRealPoint, Prod.smul_mk] using h

private theorem hFminusImAt1002 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootA : ℝ × ℝ), (F.minusSlope - rootA = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.2 (r 1) (r 0) - BandVectors.2 (r 0) (r 1))) → (F.minusSlope.2 - rootA.2
            = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r 0)).im : ℝ) - ((BandVectors.2 (r 0) (r
            1)).im : ℝ))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootA hFminusSlope
  have h := congrArg Prod.snd hFminusSlope
  simpa [GaussianRealPoint, Prod.smul_mk] using h

private theorem hleftAslopeMinus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (rootA : ℝ × ℝ), ∀ (slopeA : ℝ × ℝ), (slopeA.1 - rootA.1 = (1 / 2 : ℝ) * ((xa.re : ℝ) -
            (xa.im : ℝ))) → ((slopeA.2 - rootA.2 = (1 / 2 : ℝ) * ((xa.im : ℝ) + (xa.re : ℝ))) →
            ((ya = BandVectors.2 (p 0) (p 3)) → ((((BandVectors.2 (r 1) (r 0)).re : ℝ) = (xa.re :
            ℝ) - (ya.im : ℝ)) → ((((BandVectors.2 (r 1) (r 0)).im : ℝ) = (xa.im : ℝ) + (ya.re :
            ℝ)) → ((((BandVectors.2 (r 0) (r 1)).re : ℝ) = (xa.im : ℝ) + (ya.re : ℝ)) →
            ((((BandVectors.2 (r 0) (r 1)).im : ℝ) = -(xa.re : ℝ) + (ya.im : ℝ)) →
            ((((BandVectors.2 (p 0) (p 3)).re : ℝ) = ((BandVectors.2 (p 3) (p 0)).im : ℝ)) →
            ((((BandVectors.2 (p 0) (p 3)).im : ℝ) = -((BandVectors.2 (p 3) (p 0)).re : ℝ)) →
            ((F.minusSlope.1 - rootA.1 = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r 0)).re : ℝ) -
            ((BandVectors.2 (r 0) (r 1)).re : ℝ))) → ((F.minusSlope.2 - rootA.2 = (1 / 2 : ℝ) *
            (((BandVectors.2 (r 1) (r 0)).im : ℝ) - ((BandVectors.2 (r 0) (r 1)).im : ℝ))) →
            (F.minusSlope - slopeA = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (p 3) (p 0)
            - BandVectors.2 (p 0) (p 3))))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p r xa ya rootA slopeA hARe' hAIm' hyaA
      ha10ReR ha10ImR ha01ReR ha01ImR hRotAReR hRotAImR hFminusRe hFminusIm
  apply Prod.ext
  · calc
      F.minusSlope.1 - slopeA.1 =
          (F.minusSlope.1 - rootA.1) -
            (slopeA.1 - rootA.1) := by ring
      _ = (1 / 2 : ℝ) *
          (((BandVectors.2 (p 3) (p 0)).re : ℝ) -
            ((BandVectors.2 (p 0) (p 3)).re : ℝ)) := by
        rw [hFminusRe, hARe', ha10ReR, ha01ReR, hyaA]
        rw [hRotAReR, hRotAImR]
        ring
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (p 3) (p 0) - BandVectors.2 (p 0) (p 3))).1 := by
            simp [GaussianRealPoint, Prod.smul_mk,
              Zsqrtd.re_sub, Int.cast_sub]
  · calc
      F.minusSlope.2 - slopeA.2 =
          (F.minusSlope.2 - rootA.2) -
            (slopeA.2 - rootA.2) := by ring
      _ = (1 / 2 : ℝ) *
          (((BandVectors.2 (p 3) (p 0)).im : ℝ) -
            ((BandVectors.2 (p 0) (p 3)).im : ℝ)) := by
        rw [hFminusIm, hAIm', ha10ImR, ha01ImR, hyaA]
        rw [hRotAReR, hRotAImR]
        ring
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (p 3) (p 0) - BandVectors.2 (p 0) (p 3))).2 := by
            simp [GaussianRealPoint, Prod.smul_mk,
              Zsqrtd.im_sub, Int.cast_sub]

private theorem hjoinSlopeReA :
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
        ∀ (rootNeg : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (joinSlope.1 - rootNeg.1 = -(1 / 2 : ℝ) *
            ((↑wa.re : ℝ) - (↑wa.im : ℝ))) → (∀ (rootA : ℝ × ℝ), (rootNeg = rootA) → (joinSlope.1
            - rootA.1 = -(1 / 2 : ℝ) * ((wa.re : ℝ) - (wa.im : ℝ)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa rootNeg joinSlope hjoinSlopeRe rootA
      hrootNegA
  rw [← hrootNegA]
  exact hjoinSlopeRe

private theorem hjoinSlopeImA :
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
        ∀ (rootNeg : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (joinSlope.2 - rootNeg.2 = -(1 / 2 : ℝ) *
            ((↑wa.im : ℝ) + (↑wa.re : ℝ))) → (∀ (rootA : ℝ × ℝ), (rootNeg = rootA) → (joinSlope.2
            - rootA.2 = -(1 / 2 : ℝ) * ((wa.im : ℝ) + (wa.re : ℝ)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa rootNeg joinSlope hjoinSlopeIm rootA
      hrootNegA
  rw [← hrootNegA]
  exact hjoinSlopeIm

private theorem hleftAplusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (joinSlope : ℝ × ℝ), ∀ (rootA : ℝ × ℝ), ∀ (slopeA : ℝ × ℝ), (slopeA.1 - rootA.1 = (1 /
            2 : ℝ) * ((xa.re : ℝ) - (xa.im : ℝ))) → ((slopeA.2 - rootA.2 = (1 / 2 : ℝ) * ((xa.im
            : ℝ) + (xa.re : ℝ))) → ((ya = BandVectors.2 (p 0) (p 3)) → ((((BandVectors.2 (p 0) (p
            3)).re : ℝ) = ((BandVectors.2 (p 3) (p 0)).im : ℝ)) → ((((BandVectors.2 (p 0) (p
            3)).im : ℝ) = -((BandVectors.2 (p 3) (p 0)).re : ℝ)) → ((joinSlope.1 - rootA.1 = -(1
            / 2 : ℝ) * ((wa.re : ℝ) - (wa.im : ℝ))) → ((joinSlope.2 - rootA.2 = -(1 / 2 : ℝ) *
            ((wa.im : ℝ) + (wa.re : ℝ))) → (((wa.re : ℝ) + (xa.re : ℝ) + (ya.re : ℝ) = 0) →
            (((wa.im : ℝ) + (xa.im : ℝ) + (ya.im : ℝ) = 0) → (joinSlope - slopeA = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.2 (p 3) (p 0) + BandVectors.2 (p 0) (p 3))))))))))) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p r wa xa ya joinSlope rootA slopeA hARe'
      hAIm' hyaA hRotAReR hRotAImR hjoinSlopeReA hjoinSlopeImA hasumReR hasumImR
  apply Prod.ext
  · calc
      joinSlope.1 - slopeA.1 =
          (joinSlope.1 - rootA.1) - (slopeA.1 - rootA.1) := by ring
      _ = (1 / 2 : ℝ) * ((ya.re : ℝ) - (ya.im : ℝ)) := by
        rw [hjoinSlopeReA, hARe']
        linarith [hasumReR, hasumImR]
      _ = (1 / 2 : ℝ) *
          (((BandVectors.2 (p 3) (p 0)).re : ℝ) +
            ((BandVectors.2 (p 0) (p 3)).re : ℝ)) := by
        rw [hyaA, hRotAReR, hRotAImR]
        ring
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (p 3) (p 0) +
            BandVectors.2 (p 0) (p 3))).1 := by
        simp [GaussianRealPoint, Prod.smul_mk, Zsqrtd.re_add,
          Int.cast_add]
  · calc
      joinSlope.2 - slopeA.2 =
          (joinSlope.2 - rootA.2) - (slopeA.2 - rootA.2) := by ring
      _ = (1 / 2 : ℝ) * ((ya.im : ℝ) + (ya.re : ℝ)) := by
        rw [hjoinSlopeImA, hAIm']
        linarith [hasumReR, hasumImR]
      _ = (1 / 2 : ℝ) *
          (((BandVectors.2 (p 3) (p 0)).im : ℝ) +
            ((BandVectors.2 (p 0) (p 3)).im : ℝ)) := by
        rw [hyaA, hRotAReR, hRotAImR]
        ring
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (p 3) (p 0) +
            BandVectors.2 (p 0) (p 3))).2 := by
        simp [GaussianRealPoint, Prod.smul_mk, Zsqrtd.im_add,
          Int.cast_add]

private theorem houterBOdo :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), (F.q (a + 1).succ = p 2) → (TileOdometer (p 2) (D.tiles (a + 1)
            true) (D.functions (a + 1) true)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hqB
  simpa only [hqB] using D.odometers (a + 1) true

private theorem houterBAnc :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), (F.q (a + 1).succ = p 2) → ((0 < (p 2).1) → (AncestorOdometer (p
            2) F.outer.1.1 (D.tiles (a + 1) true) F.tile (D.functions (a + 1) true) F.odometer))
            ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hqB hBpos
  simpa only [hqB] using D.ancestors (a + 1) true
    (by rw [hqB]; exact hBpos)

private theorem hidxB2 :
    (by
      classical
      exact
        (∀ (a : Fin
            (3 : ℕ)),
        ((a + 1) + 2 = a)) ) := by
  classical
  intro a
  apply Fin.ext
  simp [Fin.val_add]; omega

private theorem hidxB1 :
    (by
      classical
      exact
        ∀ (a : Fin (3 : ℕ)), (a + 1) + 1 = a + 2 ) := by
  classical
  intro a
  apply Fin.ext
  simp [Fin.val_add]

private theorem hBocc :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (F.q a.succ = p 0) → ((F.q (a + 2).succ = p 3) → ((r 1 = p 3) → ((r 2 = p 0) → (((a + 1)
            + 2 = a) → (((a + 1) + 1 = a + 2) → (TileCentroid (D.tiles (a + 1) true) -
            TileCentroid F.tile = (1 / 2 : ℝ) • (GaussianRealPoint y - (-(GaussianRealPoint y).2,
            (GaussianRealPoint y).1)))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p r y hqA hqD hr1 hr2 hidxB2 hidxB1
  have h := (D.occurrences (a + 1) true).2.2
  simpa [hqA, hqD, hidxB2, hidxB1, y, hr1, hr2] using h

private theorem hjoinFcenter :
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
        (TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) → ((TileCentroid (D.tiles
            F.slot false) - TileCentroid Rminus = GaussianRealPoint y) → (∀ (u : ↥(TilingLattice
            C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileCentroid (D.tiles F.slot false) = TileCentroid join) → (TileCentroid join -
            TileCentroid F.tile = GaussianRealPoint y + (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r y hMcenter hcenter u join hjoinCenterEq
  rw [← hjoinCenterEq]
  rw [show TileCentroid (D.tiles F.slot false) - TileCentroid F.tile =
    (TileCentroid (D.tiles F.slot false) - TileCentroid Rminus) +
      (TileCentroid Rminus - TileCentroid F.tile) by
        ext <;> dsimp <;> ring]
  rw [hcenter, hMcenter]

private theorem hTflip :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (t : Fin
            (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple t) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        (BandVectors.1 (t 1) (t 0) = x) → (BandVectors.1 (t 0) (t 1) = I * x)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F t ht r I x hTvec
  have h := (VectorRecursionLaws t ht.1).2.2.2.2 ht 0 |>.1
  simpa [I, hTvec] using h

private theorem hrightBminus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (t : Fin (4 : ℕ) →
            CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 0) (r 1) = I * BandVectors.1
            (r 1) (r 0)) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileCentroid (D.tiles (a + 1) true) - TileCentroid F.tile = (1 / 2 : ℝ) •
            (GaussianRealPoint y - (-(GaussianRealPoint y).2, (GaussianRealPoint y).1))) →
            ((TileCentroid join - TileCentroid F.tile = GaussianRealPoint y + (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) →
            ((BandVectors.1 (t 1) (t 0) = x) → ((BandVectors.1 (t 0) (t 1) = I * x) →
            (TileCentroid join - TileCentroid (D.tiles (a + 1) true) = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.1 (t 1) (t 0) - BandVectors.1 (t 0) (t 1)))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a t r I x y hvrec hvflip u join hBocc
      hjoinFcenter hTvec hTflip
  rw [show TileCentroid join - TileCentroid (D.tiles (a + 1) true) =
    (TileCentroid join - TileCentroid F.tile) -
      (TileCentroid (D.tiles (a + 1) true) - TileCentroid F.tile) by
        ext <;> dsimp <;> ring]
  rw [hjoinFcenter, hBocc, hTvec, hTflip]
  apply Prod.ext <;>
    simp [GaussianRealPoint, x, y, I, Prod.smul_mk,
      Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_mul, Zsqrtd.im_mul, hvrec, hvflip] <;> ring


private theorem hrightBplus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (t : Fin (4 : ℕ) →
            CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 0) (r 1) = I * BandVectors.1
            (r 1) (r 0)) → ((TileCentroid (D.tiles (a + 1) true) - TileCentroid F.tile = (1 / 2 :
            ℝ) • (GaussianRealPoint y - (-(GaussianRealPoint y).2, (GaussianRealPoint y).1))) →
            ((BandVectors.1 (t 1) (t 0) = x) → ((BandVectors.1 (t 0) (t 1) = I * x) →
            ((TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1))) → (TileCentroid Rplus -
            TileCentroid (D.tiles (a + 1) true) = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1
            (t 1) (t 0) + BandVectors.1 (t 0) (t 1)))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a t r I x y hvrec hvflip hBocc hTvec
      hTflip hplusFcenter
  rw [show TileCentroid Rplus - TileCentroid (D.tiles (a + 1) true) =
    (TileCentroid Rplus - TileCentroid F.tile) -
      (TileCentroid (D.tiles (a + 1) true) - TileCentroid F.tile) by
        ext <;> dsimp <;> ring]
  rw [hplusFcenter, hBocc, hTvec, hTflip]
  apply Prod.ext <;>
    simp [GaussianRealPoint, x, y, I, Prod.smul_mk,
      Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_mul, Zsqrtd.im_mul, hvrec, hvflip] <;> ring

private theorem hBRe' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (F.q a.succ = p 0) → ((F.q (a + 2).succ = p 3) → (∀ (rootB : ℝ × ℝ), ∀ (slopeB : ℝ × ℝ),
            (slopeB.1 - rootB.1 = (if true = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (F.q (a + (1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1
            : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (1 :
            Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ)) + (1 : Fin (3 :
            ℕ))).succ)).im : ℝ))) → ((∀ (z : GaussianInt), (GaussianInt.toComplex z).re = (z.re :
            ℝ)) → ((∀ (z : GaussianInt), (GaussianInt.toComplex z).im = (z.im : ℝ)) → (((a + 1) +
            2 = a) → (((a + 1) + 1 = a + 2) → (((ya.re : ℝ) = ((BandVectors.2 (p 0) (p 3)).re :
            ℝ)) → (((ya.im : ℝ) = ((BandVectors.2 (p 0) (p 3)).im : ℝ)) → (slopeB.1 - rootB.1 =
            (1 / 2 : ℝ) * ((ya.re : ℝ) - (ya.im : ℝ))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r ya hqA hqD rootB slopeB hBRe
      toRealRe toRealIm hidxB2 hidxB1 hyaReR hyaImR
  simp only [hidxB2, hidxB1, hqA, hqD] at hBRe
  norm_num at hBRe
  rw [toRealRe] at hBRe
  rw [toRealIm] at hBRe
  rw [← hyaReR, ← hyaImR] at hBRe
  exact hBRe

private theorem hBIm' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin
            (3 : ℕ)), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (F.q a.succ = p 0) → ((F.q (a + 2).succ = p 3) → (∀ (rootB : ℝ × ℝ), ∀ (slopeB : ℝ × ℝ),
            (slopeB.2 - rootB.2 = (if true = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (F.q (a + (1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1
            : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a + (1 :
            Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ)) + (1 : Fin (3 :
            ℕ))).succ)).re : ℝ))) → ((∀ (z : GaussianInt), (GaussianInt.toComplex z).re = (z.re :
            ℝ)) → ((∀ (z : GaussianInt), (GaussianInt.toComplex z).im = (z.im : ℝ)) → (((a + 1) +
            2 = a) → (((a + 1) + 1 = a + 2) → (((ya.re : ℝ) = ((BandVectors.2 (p 0) (p 3)).re :
            ℝ)) → (((ya.im : ℝ) = ((BandVectors.2 (p 0) (p 3)).im : ℝ)) → (slopeB.2 - rootB.2 =
            (1 / 2 : ℝ) * ((ya.im : ℝ) + (ya.re : ℝ))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r ya hqA hqD rootB slopeB hBIm
      toRealRe toRealIm hidxB2 hidxB1 hyaReR hyaImR
  simp only [hidxB2, hidxB1, hqA, hqD] at hBIm
  norm_num at hBIm
  rw [toRealIm] at hBIm
  rw [toRealRe] at hBIm
  rw [← hyaImR, ← hyaReR] at hBIm
  exact hBIm

private theorem hjoinSlopeReB :
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
        ∀ (rootNeg : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (joinSlope.1 - rootNeg.1 = -(1 / 2 : ℝ) *
            ((↑wa.re : ℝ) - (↑wa.im : ℝ))) → (∀ (rootB : ℝ × ℝ), (rootNeg = rootB) → (joinSlope.1
            - rootB.1 = -(1 / 2 : ℝ) * ((wa.re : ℝ) - (wa.im : ℝ)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa rootNeg joinSlope hjoinSlopeRe rootB
      hrootNegB
  rw [← hrootNegB]
  exact hjoinSlopeRe

private theorem hjoinSlopeImB :
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
        ∀ (rootNeg : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (joinSlope.2 - rootNeg.2 = -(1 / 2 : ℝ) *
            ((↑wa.im : ℝ) + (↑wa.re : ℝ))) → (∀ (rootB : ℝ × ℝ), (rootNeg = rootB) → (joinSlope.2
            - rootB.2 = -(1 / 2 : ℝ) * ((wa.im : ℝ) + (wa.re : ℝ)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa rootNeg joinSlope hjoinSlopeIm rootB
      hrootNegB
  rw [← hrootNegB]
  exact hjoinSlopeIm

private theorem hFplusSlopeB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootB : ℝ × ℝ), (rootB = F.outerSlope) → (F.plusSlope - rootB = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.2 (r 1) (r 0) + BandVectors.2 (r 0) (r 1))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootB hrootBEq
  rw [hrootBEq]
  exact F.plus_difference

private theorem hFplusReB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootB : ℝ × ℝ), (F.plusSlope - rootB = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2
            (r 1) (r 0) + BandVectors.2 (r 0) (r 1))) → (F.plusSlope.1 - rootB.1 = (1 / 2 : ℝ) *
            (((BandVectors.2 (r 1) (r 0)).re : ℝ) + ((BandVectors.2 (r 0) (r 1)).re : ℝ))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootB hFplusSlopeB
  have h := congrArg Prod.fst hFplusSlopeB
  simpa [GaussianRealPoint, Prod.smul_mk] using h

private theorem hFplusImB :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        ∀ (rootB : ℝ × ℝ), (F.plusSlope - rootB = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2
            (r 1) (r 0) + BandVectors.2 (r 0) (r 1))) → (F.plusSlope.2 - rootB.2 = (1 / 2 : ℝ) *
            (((BandVectors.2 (r 1) (r 0)).im : ℝ) + ((BandVectors.2 (r 0) (r 1)).im : ℝ))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r rootB hFplusSlopeB
  have h := congrArg Prod.snd hFplusSlopeB
  simpa [GaussianRealPoint, Prod.smul_mk] using h

private theorem hTflipA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (t : Fin
            (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple t) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        (BandVectors.2 (t 1) (t 0) = xa) → (BandVectors.2 (t 0) (t 1) = -I * xa)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F t ht r I xa hTvecA
  have h := (VectorRecursionLaws t ht.1).2.2.2.2 ht 0 |>.2
  simpa [I, hTvecA] using h

private theorem hrightBminusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (t : Fin
            (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (joinSlope : ℝ × ℝ), ∀ (rootB : ℝ × ℝ), ∀ (slopeB : ℝ × ℝ), ((wa.re : ℝ) + (xa.re : ℝ)
            + (ya.re : ℝ) = 0) → (((wa.im : ℝ) + (xa.im : ℝ) + (ya.im : ℝ) = 0) → ((slopeB.1 -
            rootB.1 = (1 / 2 : ℝ) * ((ya.re : ℝ) - (ya.im : ℝ))) → ((slopeB.2 - rootB.2 = (1 / 2
            : ℝ) * ((ya.im : ℝ) + (ya.re : ℝ))) → ((joinSlope.1 - rootB.1 = -(1 / 2 : ℝ) *
            ((wa.re : ℝ) - (wa.im : ℝ))) → ((joinSlope.2 - rootB.2 = -(1 / 2 : ℝ) * ((wa.im : ℝ)
            + (wa.re : ℝ))) → ((BandVectors.2 (t 1) (t 0) = xa) → ((BandVectors.2 (t 0) (t 1) =
            -I * xa) → (joinSlope - slopeB = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (t 1)
            (t 0) - BandVectors.2 (t 0) (t 1)))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F t r I wa xa ya joinSlope rootB slopeB
      hasumReR hasumImR hBRe' hBIm' hjoinSlopeReB hjoinSlopeImB hTvecA hTflipA
  apply Prod.ext
  · calc
      joinSlope.1 - slopeB.1 =
          (joinSlope.1 - rootB.1) - (slopeB.1 - rootB.1) := by ring
      _ = (1 / 2 : ℝ) * ((xa.re : ℝ) - (xa.im : ℝ)) := by
        rw [hjoinSlopeReB, hBRe']
        linarith [hasumReR, hasumImR]
      _ = (1 / 2 : ℝ) *
          (((BandVectors.2 (t 1) (t 0)).re : ℝ) -
            ((BandVectors.2 (t 0) (t 1)).re : ℝ)) := by
        rw [hTvecA, hTflipA]
        norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (t 1) (t 0) -
            BandVectors.2 (t 0) (t 1))).1 := by
        simp [GaussianRealPoint, Prod.smul_mk, Zsqrtd.re_sub,
          Int.cast_sub]
  · calc
      joinSlope.2 - slopeB.2 =
          (joinSlope.2 - rootB.2) - (slopeB.2 - rootB.2) := by ring
      _ = (1 / 2 : ℝ) * ((xa.im : ℝ) + (xa.re : ℝ)) := by
        rw [hjoinSlopeImB, hBIm']
        linarith [hasumReR, hasumImR]
      _ = (1 / 2 : ℝ) *
          (((BandVectors.2 (t 1) (t 0)).im : ℝ) -
            ((BandVectors.2 (t 0) (t 1)).im : ℝ)) := by
        rw [hTvecA, hTflipA]
        norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (t 1) (t 0) -
            BandVectors.2 (t 0) (t 1))).2 := by
        simp [GaussianRealPoint, Zsqrtd.im_sub,
          Int.cast_sub]

private theorem hrightBplusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (t : Fin
            (4 : ℕ) → CircleCoordinates),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        ∀ (rootB : ℝ × ℝ), ∀ (slopeB : ℝ × ℝ), (((BandVectors.2 (r 1) (r 0)).re : ℝ) = (xa.re :
            ℝ) - (ya.im : ℝ)) → ((((BandVectors.2 (r 1) (r 0)).im : ℝ) = (xa.im : ℝ) + (ya.re :
            ℝ)) → ((((BandVectors.2 (r 0) (r 1)).re : ℝ) = (xa.im : ℝ) + (ya.re : ℝ)) →
            ((((BandVectors.2 (r 0) (r 1)).im : ℝ) = -(xa.re : ℝ) + (ya.im : ℝ)) → ((slopeB.1 -
            rootB.1 = (1 / 2 : ℝ) * ((ya.re : ℝ) - (ya.im : ℝ))) → ((slopeB.2 - rootB.2 = (1 / 2
            : ℝ) * ((ya.im : ℝ) + (ya.re : ℝ))) → ((F.plusSlope.1 - rootB.1 = (1 / 2 : ℝ) *
            (((BandVectors.2 (r 1) (r 0)).re : ℝ) + ((BandVectors.2 (r 0) (r 1)).re : ℝ))) →
            ((F.plusSlope.2 - rootB.2 = (1 / 2 : ℝ) * (((BandVectors.2 (r 1) (r 0)).im : ℝ) +
            ((BandVectors.2 (r 0) (r 1)).im : ℝ))) → ((BandVectors.2 (t 1) (t 0) = xa) →
            ((BandVectors.2 (t 0) (t 1) = -I * xa) → (F.plusSlope - slopeB = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.2 (t 1) (t 0) + BandVectors.2 (t 0) (t 1)))))))))))) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F t r I xa ya rootB slopeB ha10ReR ha10ImR
      ha01ReR ha01ImR hBRe' hBIm' hFplusReB hFplusImB hTvecA hTflipA
  apply Prod.ext
  · calc
      F.plusSlope.1 - slopeB.1 =
          (F.plusSlope.1 - rootB.1) - (slopeB.1 - rootB.1) := by ring
      _ = (1 / 2 : ℝ) * ((xa.re : ℝ) + (xa.im : ℝ)) := by
        rw [hFplusReB, hBRe', ha10ReR, ha01ReR]
        ring
      _ = (1 / 2 : ℝ) *
          (((BandVectors.2 (t 1) (t 0)).re : ℝ) +
            ((BandVectors.2 (t 0) (t 1)).re : ℝ)) := by
        rw [hTvecA, hTflipA]
        norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (t 1) (t 0) +
            BandVectors.2 (t 0) (t 1))).1 := by
        simp [GaussianRealPoint, Zsqrtd.re_add,
          Int.cast_add]
  · calc
      F.plusSlope.2 - slopeB.2 =
          (F.plusSlope.2 - rootB.2) - (slopeB.2 - rootB.2) := by ring
      _ = (1 / 2 : ℝ) * ((xa.im : ℝ) - (xa.re : ℝ)) := by
        rw [hFplusImB, hBIm', ha10ImR, ha01ImR]
        ring
      _ = (1 / 2 : ℝ) *
          (((BandVectors.2 (t 1) (t 0)).im : ℝ) +
            ((BandVectors.2 (t 0) (t 1)).im : ℝ)) := by
        rw [hTvecA, hTflipA]
        norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
        ring
      _ = ((1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.2 (t 1) (t 0) +
            BandVectors.2 (t 0) (t 1))).2 := by
        simp [GaussianRealPoint, Zsqrtd.im_add,
          Int.cast_add]

end SecondNewerRowsGeometry

namespace SecondParentPlacements

private theorem firstParentPlacement :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (hp : ProperBandQuadruple p), (![F.q (0 : Fin (4 : ℕ)), F.q
            a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 :
            ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 :
            Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 :
            ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 :
            Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)),
            p (3 : Fin (4 : ℕ))]) → ((F.slot = a + (1 : Fin (3 : ℕ)) → C.1.1.1 = (1 : ℤ) →
            UnitOccurrenceOrientation p (1 : Fin (3 : ℕ)) orientation) → ((F.slot = a + (2 : Fin
            (3 : ℕ)) → C.1.1.1 = (1 : ℤ) → UnitOccurrenceOrientation p (2 : Fin (3 : ℕ))
            orientation) → ((F.slot ≠ a) → (∀ (t : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple t) → ((t (0 : Fin (4 : ℕ)) = p (2 : Fin (4 : ℕ))) → ((t (1 : Fin
            (4 : ℕ)) = p (3 : Fin (4 : ℕ))) → ((F.slot = a + (2 : Fin (3 : ℕ)) → C.1.1.1 = (1 :
            ℤ) → UnitOccurrenceOrientation t (0 : Fin (3 : ℕ)) orientation) → ((0 < (F.q
            F.slot.succ).1) → (((F.q F.slot.succ).1 < (F.q 0).1) → ((AncestorOdometer (F.q
            F.slot.succ) F.outer.1.1 (D.tiles F.slot false) F.tile (D.functions F.slot false)
            F.odometer) → ((TileOdometer (F.q F.slot.succ) (D.tiles F.slot false) (D.functions
            F.slot false)) → ((∃ (s : ℝ × ℝ), PartialOdometerSlope (D.functions F.slot false) =
            some s) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → ((r 1 = C.1.1) → (
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
            (r 0)) → (((BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).re + (BandVectors.1 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).re + (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).re = (0 : ℤ)) → (((BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).im +
            (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))).im + (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).im = (0 : ℤ)) → ((BandPrototile (F.q F.slot.succ) (D.tiles F.slot false)) →
            ((FootprintVertices (D.tiles F.slot false) ⊆ FootprintVertices F.tile) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = (if false = true then
            (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (F.slot
            + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = -(1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))) -
            (-(GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))))).2,
            (GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))))).1))) →
            ((TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) → ((-BandVectors.1 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) - BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
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
            GaussianRealPoint y) → ((
        let y := BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))); y ∈ TilingLattice C) → (∀ (u :
            ↥(TilingLattice C)), (Rminus = TileTranslation base (↑u : GaussianInt)) → (
        let join : ProtoTile := TileTranslation base (u + y)
        (join = TileTranslation Rminus y) → ((BandPrototile C.1.1 join) → ((
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
            : ℕ))))) → ((TileCentroid (D.tiles F.slot false) = TileCentroid join) →
            ((BandPrototile C.1.1 (D.tiles F.slot false)) → (((D.tiles F.slot false).cells =
            join.cells ∧ ((D.tiles F.slot false).cells = ∅ → (D.tiles F.slot false).anchor =
            join.anchor)) → ((TileOdometer C.1.1 (TileTranslation base ((↑u : GaussianInt) +
            BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))) (D.functions F.slot false)) →
            ((AncestorOdometer C.1.1 F.outer.1.1 (TileTranslation base ((↑u : GaussianInt) +
            BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))) F.tile (D.functions F.slot false)
            F.odometer) → ((∀ (c : CircleCoordinates), ∀ (T : ProtoTile), (0 : ℤ) < c.1 →
            BandPrototile c T → Finset.Nonempty T.cells) → (((D.tiles F.slot
            false).cells.Nonempty) → ((join.cells.Nonempty) → ((FootprintVertices
            (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ))))) = FootprintVertices (D.tiles F.slot false)) → ((FootprintVertices
            (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ))))) ⊆ FootprintVertices F.tile) → ((BandSubtileOccurrence F.q F.tile F.slot false
            (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))))) → ((F.q (0 : Fin (4 : ℕ)) = ((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p
            (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1,
            (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 :
            ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2)) →
            ((F.q a.succ = p 0) → ((F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → (∀
            (rootNeg : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (PartialOdometerSlope F.odometer = some
            rootNeg) → ((PartialOdometerSlope (D.functions F.slot false) = some joinSlope) →
            ((joinSlope.1 - rootNeg.1 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ)))).re : ℝ) - (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).im : ℝ))) →
            ((joinSlope.2 - rootNeg.2 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ)))).im : ℝ) + (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).re : ℝ))) →
            ((rootNeg = F.outerSlope) → ((F.slot = a + (1 : Fin (3 : ℕ))) → ((r 1 = p 2) → ((r 2
            = p 3) → ((r 3 = p 0) → (∀ (hApos : 0 < (p 0).1), (F.q a.succ = p 0) → ((0 < (F.q
            a.succ).1) → (∀ (rootSlope : ℝ × ℝ), ∀ (aSlope : ℝ × ℝ), (PartialOdometerSlope
            F.odometer = some rootSlope) → ((PartialOdometerSlope (D.functions a true) = some
            aSlope) → ((aSlope.1 - rootSlope.1 = (if true = true then (1 : ℝ) else (-1 : ℝ)) * (1
            / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3
            : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a +
            (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((aSlope.2 - rootSlope.2 = (if true = true then
            (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
            ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a +
            (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((rootSlope
            = F.outerSlope) → (
        let directOuter : BandCircle :=
          ⟨⟨p 0, ⟨Or.inl hApos, ⟨p, hp.1, 0, rfl⟩⟩⟩, hApos⟩
        (directOuter.1.1 = F.q a.succ) → ((p 2 = C.1.1) → ((TileOdometer (p 0) (D.tiles a true)
            (D.functions a true)) → ((BandPrototile (p 0) (D.tiles a true)) → ((AncestorOdometer
            (p (0 : Fin (4 : ℕ))) F.outer.1.1 (D.tiles a true) F.tile (D.functions a true)
            F.odometer) → ((BandVectors.1 (p 2) (p 0) = x) → ((BandVectors.2 (p 2) (p 0) = xa) →
            ((BandVectors.1 (p 0) (p 2) = I * x) → ((BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (2 :
            Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ)))) → ((Fin.succ (1 : Fin 3) = 2) → ((TileCentroid (D.tiles a true) -
            TileCentroid F.tile = (1 / 2 : ℝ) • (GaussianRealPoint y - (-(GaussianRealPoint y).2,
            (GaussianRealPoint y).1))) → ((aSlope.1 - rootSlope.1 = (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).re : ℝ) - (↑(BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ)))).im : ℝ))) → ((aSlope.2 - rootSlope.2 = (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ)))).re : ℝ))) → (((BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ)))).re + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))).re + (BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ)))).re = (0 : ℤ)) → (((BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))).im + (BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ)))).im = (0 : ℤ)) → (((wa.re : ℝ) + (xa.re : ℝ) + (ya.re :
            ℝ) = 0) → (((wa.im : ℝ) + (xa.im : ℝ) + (ya.im : ℝ) = 0) → ((joinSlope - aSlope = (1
            / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (0 : Fin (4 :
            ℕ))) - BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ))))) → ((F.plusSlope -
            rootSlope = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))
            + BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3
            : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))) → ((F.plusSlope.1 - rootSlope.1 = (1 /
            2 : ℝ) * (((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4
            : ℕ))))).re + ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))).re)) → ((F.plusSlope.2 - rootSlope.2 = (1 / 2 : ℝ) *
            (((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 :
            ℕ))))).im + ((GaussianInt.toComplex : GaussianInt → ℂ) (BandVectors.2 (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ))))).im)) → (((BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))).re =
            (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))).re - (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).im) → (((BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))).im = (BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).re) → (((BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).re = (BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).im + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).re) → (((BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).im = -(BandVectors.2 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).re + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).im) → (((BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) +
            BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ)))).re = (BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).re + (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).im) → (((BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) +
            BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ)))).im = (BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).im - (BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).re) → ((F.plusSlope.1 - rootSlope.1 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ)))).re : ℝ) + (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).re : ℝ))) → ((F.plusSlope.2 - rootSlope.2 = (1 / 2 : ℝ) * ((↑(BandVectors.2
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (0 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).im : ℝ))) → ((F.plusSlope - aSlope = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) + BandVectors.2 (p (0 :
            Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ))))) → (Nonempty (P4458T1BoundaryPlacement F
            D)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            ))))))))))))))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hp hstep hB hD selected t ht ht0 ht1
      olderChart hCpositive hstrict hselectedAnc hselectedOdo hnegativeSlope r hr hRparent I w x
      y wa xa ya hvsum hasum hvrec harec hvflip haflip hvsumRe hvsumIm hUband hUfoot hUcent
      hUcenter hMcenter hcenterVector hcenterRe hcenterIm hcenter hyLattice u huRminus join
      hjoin_eq hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC hjoinCells hjoinOdo
      hjoinAncestor positiveCells hUnonempty hJoinNonemptyBase hjoinFootEq hjoinFoot
      hjoinOccurrence hq0 hqA hqB hqD rootNeg joinSlope hrootNeg hjoinSlope hjoinSlopeRe
      hjoinSlopeIm hrootNegEq hSB hr1 hr2 hr3 hApos hAcoord hApos' rootSlope aSlope hrootSlope
      haSlope hARe hAIm hrootSlopeEq directOuter hparentA hparentB houterOdo houterBand houterAnc
      hBA haBA hvAB haAB hidx2 hAocc hARe' hAIm' hasumRe hasumIm hasumReR hasumImR
      hminusSlopeOffset hFplusSlope hFplusRe hFplusIm ha10Re ha10Im ha01Re ha01Im hplusReVec
      hplusImVec hFplusRe' hFplusIm' hplusSlopeOffset
  let G : P4458T1BoundaryFrame C orientation base join Rplus
      (D.functions F.slot false) hplus := {
    outer := directOuter
    q := p
    proper := hp
    slot := 1
    child := rfl
    parent := hparentB
    tile := D.tiles a true
    odometer := D.functions a true
    outer_odo := houterOdo
    minus_odo := hjoinOdo
    plus_odo := F.plus_odo
    outer_band := houterBand
    base_band := F.base_band
    minus_family := hjoinFamily
    plus_family := F.plus_family
    chart := by
      intro hunit
      exact hB hSB (by simpa only [hparentB] using hunit)
    minus_centroid := by
      rw [hidx2]
      rw [show TileCentroid join - TileCentroid (D.tiles a true) =
        (TileCentroid join - TileCentroid Rminus) +
          (TileCentroid Rminus - TileCentroid F.tile) -
          (TileCentroid (D.tiles a true) - TileCentroid F.tile) by
            ext <;> dsimp <;> ring]
      rw [← hjoinCenterEq, hcenter, hMcenter, hAocc,
        hvflip, hvrec, hBA, hvAB]
      apply Prod.ext <;>
        simp [GaussianRealPoint, I, Prod.smul_mk,
          Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
    plus_centroid := by
      rw [hidx2]
      rw [show TileCentroid Rplus - TileCentroid (D.tiles a true) =
        (TileCentroid Rplus - TileCentroid F.tile) -
          (TileCentroid (D.tiles a true) - TileCentroid F.tile) by
            ext <;> dsimp <;> ring]
      have hPcenter : TileCentroid Rplus - TileCentroid F.tile =
          (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1)) :=
                BoundaryFrameJoinGeometry.plusCentroid C orientation base Rminus Rplus hminus
                    hplus F
      rw [hPcenter, hAocc, hvflip, hvrec, hBA, hvAB]
      apply Prod.ext <;>
        simp [GaussianRealPoint, I, Prod.smul_mk,
          Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
    outerSlope := aSlope
    minusSlope := joinSlope
    plusSlope := F.plusSlope
    slope_outer := haSlope
    slope_minus := hjoinSlope
    slope_plus := F.slope_plus
    minus_difference := hminusSlopeOffset
    plus_difference := hplusSlopeOffset
  }
  have houterEq : G.outer.1.1 = F.q a.succ := hparentA
  have hright : P4458T1BoundarySide F join Rplus
      (D.functions F.slot false) hplus :=
    .recursive G a houterEq houterAnc
  have hFminusSlope := SecondNewerRowsGeometry.hFminusSlopeAt641 C orientation base Rminus
      Rplus hminus hplus F rootSlope hrootSlopeEq
  have hFminusRe := SecondNewerRowsGeometry.hFminusReAt646 C orientation base Rminus Rplus
      hminus hplus F rootSlope hFminusSlope
  have hFminusIm := SecondNewerRowsGeometry.hFminusImAt652 C orientation base Rminus Rplus
      hminus hplus F rootSlope hFminusSlope
  have hrootSame : rootNeg = rootSlope := hrootNegEq.trans hrootSlopeEq.symm
  rw [hrootSame] at hjoinSlopeRe hjoinSlopeIm
  have ha10ReR : ((BandVectors.2 (r 1) (r 0)).re : ℝ) =
      (xa.re : ℝ) - (ya.im : ℝ) := by exact_mod_cast ha10Re
  have ha10ImR : ((BandVectors.2 (r 1) (r 0)).im : ℝ) =
      (xa.im : ℝ) + (ya.re : ℝ) := by exact_mod_cast ha10Im
  have ha01ReR : ((BandVectors.2 (r 0) (r 1)).re : ℝ) =
      (xa.im : ℝ) + (ya.re : ℝ) := by exact_mod_cast ha01Re
  have ha01ImR : ((BandVectors.2 (r 0) (r 1)).im : ℝ) =
      -(xa.re : ℝ) + (ya.im : ℝ) := by exact_mod_cast ha01Im
  have hdirectSlope := SecondNewerRowsGeometry.hdirectSlope C orientation base Rminus Rplus
      hminus hplus F joinSlope rootSlope hjoinSlopeIm hjoinSlopeRe hasumReR hasumImR
      hFminusRe hFminusIm ha10ReR ha10ImR ha01ReR ha01ImR
  have hleftCent := SecondNewerRowsGeometry.hleftCent C orientation base Rminus Rplus hminus
      hplus F D hcenter u hjoinCenterEq
  have htC : t 0 = C.1.1 := ht0.trans hparentB
  have hleftTouch := SecondNewerRowsGeometry.hleftTouch C orientation base Rminus Rplus
      hminus hplus F p t ht ht0 ht1 u hjoinFamily hr1 hr2 hleftCent htC
      (SecondNewerRowsGeometry.hbaseT C orientation base Rminus Rplus hminus hplus F t htC)
  have hleftAdjacent := SecondNewerRowsGeometry.hleftAdjacent C orientation base Rminus Rplus
      hminus hplus F D p t ht ht0 ht1 u hjoinOdo joinSlope hjoinSlope hr1 hr2 hdirectSlope
      hleftCent htC
  have hMnonempty := SecondNewerRowsGeometry.hMnonempty C orientation base Rminus Rplus
      hminus hplus F positiveCells
  refine ⟨⟨join, hjoinCells.1.symm, hjoinOdo, hjoinAncestor,
    hjoinOccurrence, .direct (SecondNewerRowsGeometry.leftString C orientation base Rminus
        Rplus hminus hplus F D a p hp hstep hB hD selected t olderChart hCpositive hstrict
        hselectedAnc hselectedOdo hnegativeSlope hr hRparent hvsum hasum hvrec harec hvflip
        haflip hvsumRe hvsumIm hUband hUfoot hUcent hUcenter hMcenter hcenterVector hcenterRe
        hcenterIm hcenter hyLattice u huRminus hjoin_eq hjoinBand hjoinFamily hjoinCenter
        hjoinCenterEq hUbandC hjoinCells hjoinOdo hjoinAncestor hUnonempty hJoinNonemptyBase
        hjoinFootEq hjoinFoot hjoinOccurrence hq0 hqA hqB hqD rootNeg joinSlope hrootNeg
        hjoinSlope hrootNegEq hSB hr1 hr2 hr3 hAcoord hApos' rootSlope hjoinSlopeIm
        hjoinSlopeRe aSlope hrootSlope haSlope hARe hAIm hrootSlopeEq hparentA
        hparentB houterOdo houterBand houterAnc hBA haBA hvAB haAB hidx2 hAocc hARe' hAIm'
        hasumRe hasumIm hasumReR hasumImR hminusSlopeOffset hFplusSlope hFplusRe hFplusIm
        ha10Re ha10Im ha01Re ha01Im hplusReVec hplusImVec hFplusRe' hFplusIm'
        hplusSlopeOffset houterEq hright hFminusSlope hFminusRe hFminusIm ha10ReR ha10ImR
        ha01ReR ha01ImR hdirectSlope hleftCent hleftTouch hleftAdjacent hMnonempty
        (SecondNewerRowsGeometry.hJnonempty C orientation base Rminus Rplus hminus hplus F D
        u hjoinCells hUnonempty) (SecondNewerRowsGeometry.hleftNe C orientation base Rminus
        Rplus hminus hplus F u hleftTouch hMnonempty) (SecondNewerRowsGeometry.hnonunit C
        orientation base Rminus Rplus hminus hplus F a p t ht htC)) hleftAdjacent, hright⟩⟩

private theorem secondParentPlacement :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (hp : ProperBandQuadruple p), (F.slot = a + (2 : Fin (3 : ℕ)) →
            C.1.1.1 = (1 : ℤ) → UnitOccurrenceOrientation p (2 : Fin (3 : ℕ)) orientation) → (∀
            (t : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple t) → ((t (0 : Fin (4 :
            ℕ)) = p (2 : Fin (4 : ℕ))) → ((t (1 : Fin (4 : ℕ)) = p (3 : Fin (4 : ℕ))) → ((F.slot
            = a + (2 : Fin (3 : ℕ)) → C.1.1.1 = (1 : ℤ) → UnitOccurrenceOrientation t (0 : Fin (3
            : ℕ)) orientation) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 0) (r 1) = I * BandVectors.1
            (r 1) (r 0)) → ((TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y) →
            (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (
        let join := TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ)))); join ∈ RegularTileFamily base (TilingLattice C)) → ((TileCentroid (D.tiles
            F.slot false) = TileCentroid join) → (((D.tiles F.slot false).cells = join.cells ∧
            ((D.tiles F.slot false).cells = ∅ → (D.tiles F.slot false).anchor = join.anchor)) →
            ((TileOdometer C.1.1 (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))) (D.functions F.slot false)) → ((AncestorOdometer
            C.1.1 F.outer.1.1 (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))) F.tile (D.functions F.slot false) F.odometer) →
            ((BandSubtileOccurrence F.q F.tile F.slot false (TileTranslation base ((↑u :
            GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))))) → ((F.q a.succ = p 0) →
            ((F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → (∀ (rootNeg : ℝ × ℝ), ∀
            (joinSlope : ℝ × ℝ), (PartialOdometerSlope (D.functions F.slot false) = some
            joinSlope) → ((joinSlope.1 - rootNeg.1 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).re : ℝ) - (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ)))).im : ℝ))) → ((joinSlope.2 - rootNeg.2 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ)))).re : ℝ))) → ((rootNeg = F.outerSlope) → ((F.slot = a + (2 : Fin (3 : ℕ))) →
            ((r 1 = p 3) → ((r 2 = p 0) → ((r 3 = p 2) → (∀ (hApos : 0 < (p 0).1), ((0 : ℤ) < (p
            (2 : Fin (4 : ℕ))).1) → (∀ (rootA : ℝ × ℝ), ∀ (slopeA : ℝ × ℝ), (PartialOdometerSlope
            (D.functions a true) = some slopeA) → (∀ (rootB : ℝ × ℝ), ∀ (slopeB : ℝ × ℝ),
            (PartialOdometerSlope (D.functions (a + (1 : Fin (3 : ℕ))) true) = some slopeB) →
            ((slopeB.1 - rootB.1 = (if true = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (F.q (a + (1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1
            : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (1 :
            Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ)) + (1 : Fin (3 :
            ℕ))).succ)).im : ℝ))) → ((slopeB.2 - rootB.2 = (if true = true then (1 : ℝ) else (-1
            : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (1 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (F.q (a + (1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1
            : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((rootB = F.outerSlope) → (
        let recursiveOuter : BandCircle :=
          ⟨⟨p 0, ⟨Or.inl hApos, ⟨p, hp.1, 0, rfl⟩⟩⟩, hApos⟩
        (recursiveOuter.1.1 = F.q a.succ) → ((TileOdometer (p (0 : Fin (4 : ℕ))) (D.tiles a true)
            (D.functions a true)) → ((BandPrototile (p 0) (D.tiles a true)) → ((p 3 = C.1.1) →
            ((∀ (z : GaussianInt), (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀ (z :
            GaussianInt), (GaussianInt.toComplex z).im = (z.im : ℝ)) → ((TileCentroid Rminus -
            TileCentroid (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (p (3
            : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) - BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (3 :
            Fin (4 : ℕ))))) → ((slopeA.1 - rootA.1 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).re : ℝ) - (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).im : ℝ))) → ((slopeA.2 - rootA.2 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 :
            ℕ)))).re : ℝ))) → ((ya = BandVectors.2 (p 0) (p 3)) → ((((BandVectors.2 (r 1) (r
            0)).re : ℝ) = (xa.re : ℝ) - (ya.im : ℝ)) → ((((BandVectors.2 (r 1) (r 0)).im : ℝ) =
            (xa.im : ℝ) + (ya.re : ℝ)) → ((((BandVectors.2 (r 0) (r 1)).re : ℝ) = (xa.im : ℝ) +
            (ya.re : ℝ)) → ((((BandVectors.2 (r 0) (r 1)).im : ℝ) = -(xa.re : ℝ) + (ya.im : ℝ)) →
            ((((BandVectors.2 (p 0) (p 3)).re : ℝ) = ((BandVectors.2 (p 3) (p 0)).im : ℝ)) →
            ((((BandVectors.2 (p 0) (p 3)).im : ℝ) = -((BandVectors.2 (p 3) (p 0)).re : ℝ)) →
            ((F.minusSlope.1 - rootA.1 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4
            : ℕ)))).re : ℝ) - (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).re : ℝ))) →
            ((F.minusSlope.2 - rootA.2 = (1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4
            : ℕ)))).im : ℝ) - (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))).im : ℝ))) →
            ((rootNeg = rootA) → (((wa.re : ℝ) + (xa.re : ℝ) + (ya.re : ℝ) = 0) → (((wa.im : ℝ) +
            (xa.im : ℝ) + (ya.im : ℝ) = 0) → (Nonempty (P4458T1BoundaryPlacement F
            D)))))))))))))))))))))))))))))))))))))))))))))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hp hD t ht ht0 ht1 olderChart r I x
      y wa xa ya hvrec hvflip hMcenter hcenter u join hjoinFamily hjoinCenterEq hjoinCells
      hjoinOdo hjoinAncestor hjoinOccurrence hqA hqB hqD rootNeg joinSlope hjoinSlope
      hjoinSlopeRe hjoinSlopeIm hrootNegEq hSD hr1 hr2 hr3 hApos hBpos rootA slopeA hslopeA rootB
      slopeB hslopeB hBRe hBIm hrootBEq recursiveOuter houterA houterAOdo houterABand hparentD
      toRealRe toRealIm hleftAminus hARe' hAIm' hyaA ha10ReR ha10ImR ha01ReR ha01ImR hRotAReR
      hRotAImR hFminusRe hFminusIm hrootNegA hasumReR hasumImR
  let Gleft : P4458T1BoundaryFrame C orientation base Rminus join
      hminus (D.functions F.slot false) := {
    outer := recursiveOuter
    q := p
    proper := hp
    slot := 2
    child := rfl
    parent := hparentD
    tile := D.tiles a true
    odometer := D.functions a true
    outer_odo := houterAOdo
    minus_odo := F.minus_odo
    plus_odo := hjoinOdo
    outer_band := houterABand
    base_band := F.base_band
    minus_family := F.minus_family
    plus_family := hjoinFamily
    chart := by
      intro hunit
      exact hD hSD (by simpa only [hparentD] using hunit)
    minus_centroid := hleftAminus
    plus_centroid := (SecondNewerRowsGeometry.hleftAplus C orientation base Rminus Rplus
        hminus hplus F D a p hcenter u hjoinCenterEq hr1 hr2 hleftAminus)
    outerSlope := slopeA
    minusSlope := F.minusSlope
    plusSlope := joinSlope
    slope_outer := hslopeA
    slope_minus := F.slope_minus
    slope_plus := hjoinSlope
    minus_difference := (SecondNewerRowsGeometry.hleftAslopeMinus C orientation base Rminus
        Rplus hminus hplus F p rootA slopeA hARe' hAIm' hyaA ha10ReR ha10ImR ha01ReR ha01ImR
        hRotAReR hRotAImR hFminusRe hFminusIm)
    plus_difference := (SecondNewerRowsGeometry.hleftAplusSlope C orientation base Rminus
        Rplus hminus hplus F p joinSlope rootA slopeA hARe' hAIm' hyaA hRotAReR hRotAImR
        (SecondNewerRowsGeometry.hjoinSlopeReA C orientation base Rminus Rplus hminus hplus F
        rootNeg joinSlope hjoinSlopeRe rootA hrootNegA)
        (SecondNewerRowsGeometry.hjoinSlopeImA C orientation base Rminus Rplus hminus hplus F
        rootNeg joinSlope hjoinSlopeIm rootA hrootNegA) hasumReR hasumImR)
  }
  have hleftOuterEq : Gleft.outer.1.1 = F.q a.succ := houterA
  have hleft : P4458T1BoundarySide F Rminus join
      hminus (D.functions F.slot false) :=
    .recursive Gleft a hleftOuterEq (SecondNewerRowsGeometry.houterAAnc C orientation base
        Rminus Rplus hminus hplus F D a p hqA hApos)
  let outerB : BandCircle :=
    ⟨⟨p 2, ⟨Or.inl hBpos, ⟨p, hp.1, 2, rfl⟩⟩⟩, hBpos⟩
  have houterB : outerB.1.1 = F.q (a + 1).succ := by
    simp [outerB, hqB]
  have houterBOdo := SecondNewerRowsGeometry.houterBOdo C orientation base Rminus Rplus
      hminus hplus F D a p hqB
  have houterBBand : BandPrototile (p 2) (D.tiles (a + 1) true) :=
    TileOdometerBandPrototile (p 2) (D.tiles (a + 1) true)
      (D.functions (a + 1) true) houterBOdo
  have ht1C : t 1 = C.1.1 := ht1.trans hparentD
  have hidxB2 := SecondNewerRowsGeometry.hidxB2 a
  have hidxB1 := SecondNewerRowsGeometry.hidxB1 a
  have hBocc := SecondNewerRowsGeometry.hBocc C orientation base Rminus Rplus hminus hplus F
      D a p hqA hqD hr1 hr2 hidxB2 hidxB1
  have hTvec : BandVectors.1 (t 1) (t 0) = x := by
    simp [ht0, ht1, hr1, hr3, x]
  have hTflip := SecondNewerRowsGeometry.hTflip C orientation base Rminus Rplus hminus hplus
      F t ht hTvec
  have hrightBminus := SecondNewerRowsGeometry.hrightBminus C orientation base Rminus Rplus
      hminus hplus F D a t hvrec hvflip u hBocc (SecondNewerRowsGeometry.hjoinFcenter C
      orientation base Rminus Rplus hminus hplus F D hMcenter hcenter u hjoinCenterEq) hTvec
      hTflip
  have hrightBplus := SecondNewerRowsGeometry.hrightBplus C orientation base Rminus Rplus
      hminus hplus F D a t hvrec hvflip hBocc hTvec hTflip
      (BoundaryFrameJoinGeometry.plusCentroid C orientation base Rminus Rplus hminus hplus F)
  have hyaReR : (ya.re : ℝ) =
      ((BandVectors.2 (p 0) (p 3)).re : ℝ) := by rw [hyaA]
  have hyaImR : (ya.im : ℝ) =
      ((BandVectors.2 (p 0) (p 3)).im : ℝ) := by rw [hyaA]
  have hBRe' := SecondNewerRowsGeometry.hBRe' C orientation base Rminus Rplus hminus hplus F
      a p hqA hqD rootB slopeB hBRe toRealRe toRealIm hidxB2 hidxB1 hyaReR hyaImR
  have hBIm' := SecondNewerRowsGeometry.hBIm' C orientation base Rminus Rplus hminus hplus F
      a p hqA hqD rootB slopeB hBIm toRealRe toRealIm hidxB2 hidxB1 hyaReR hyaImR
  have hrootNegB : rootNeg = rootB := hrootNegEq.trans hrootBEq.symm
  have hFplusSlopeB := SecondNewerRowsGeometry.hFplusSlopeB C orientation base Rminus Rplus
      hminus hplus F rootB hrootBEq
  have hTvecA : BandVectors.2 (t 1) (t 0) = xa := by
    simp [ht0, ht1, hr1, hr3, xa]
  have hTflipA := SecondNewerRowsGeometry.hTflipA C orientation base Rminus Rplus hminus
      hplus F t ht hTvecA
  have hrightBminusSlope := SecondNewerRowsGeometry.hrightBminusSlope C orientation base
      Rminus Rplus hminus hplus F t joinSlope rootB slopeB hasumReR hasumImR hBRe' hBIm'
      (SecondNewerRowsGeometry.hjoinSlopeReB C orientation base Rminus Rplus hminus hplus F
      rootNeg joinSlope hjoinSlopeRe rootB hrootNegB) (SecondNewerRowsGeometry.hjoinSlopeImB
      C orientation base Rminus Rplus hminus hplus F rootNeg joinSlope hjoinSlopeIm rootB
      hrootNegB) hTvecA hTflipA
  have hrightBplusSlope := SecondNewerRowsGeometry.hrightBplusSlope C orientation base Rminus
      Rplus hminus hplus F t rootB slopeB ha10ReR ha10ImR ha01ReR ha01ImR hBRe' hBIm'
      (SecondNewerRowsGeometry.hFplusReB C orientation base Rminus Rplus hminus hplus F rootB
      hFplusSlopeB) (SecondNewerRowsGeometry.hFplusImB C orientation base Rminus Rplus hminus
      hplus F rootB hFplusSlopeB) hTvecA hTflipA
  let Gright : P4458T1BoundaryFrame C orientation base join Rplus
      (D.functions F.slot false) hplus := {
    outer := outerB
    q := t
    proper := ht
    slot := 0
    child := by simpa [outerB] using ht0
    parent := ht1C
    tile := D.tiles (a + 1) true
    odometer := D.functions (a + 1) true
    outer_odo := houterBOdo
    minus_odo := hjoinOdo
    plus_odo := F.plus_odo
    outer_band := houterBBand
    base_band := F.base_band
    minus_family := hjoinFamily
    plus_family := F.plus_family
    chart := by
      intro hunit
      exact olderChart hSD (by simpa only [ht1C] using hunit)
    minus_centroid := hrightBminus
    plus_centroid := hrightBplus
    outerSlope := slopeB
    minusSlope := joinSlope
    plusSlope := F.plusSlope
    slope_outer := hslopeB
    slope_minus := hjoinSlope
    slope_plus := F.slope_plus
    minus_difference := hrightBminusSlope
    plus_difference := hrightBplusSlope
  }
  have hrightOuterEq : Gright.outer.1.1 = F.q (a + 1).succ := houterB
  have hrightParent : Gright.outer.1.1 = F.q (a + 1).succ := hrightOuterEq
  have hright : P4458T1BoundarySide F join Rplus
      (D.functions F.slot false) hplus :=
    .recursive Gright (a + 1) hrightParent ((show
        AncestorOdometer Gright.outer.1.1 F.outer.1.1 Gright.tile F.tile Gright.odometer
        F.odometer
      from by
        classical
        simpa only using ((SecondNewerRowsGeometry.houterBAnc C orientation base Rminus Rplus
            hminus hplus F D
                a p hqB hBpos))))
  refine ⟨⟨join, hjoinCells.1.symm, hjoinOdo, hjoinAncestor,
  hjoinOccurrence, hleft, hright⟩⟩

end SecondParentPlacements

namespace SecondParentCases

private theorem directParentCase :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), (ProperBandQuadruple p) → ((![F.q (0 : Fin (4 : ℕ)), F.q a.succ,
            F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p
            (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
            ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
            GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2
            - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 :
            ℕ))]) → ((F.slot = a + (1 : Fin (3 : ℕ)) → C.1.1.1 = (1 : ℤ) →
            UnitOccurrenceOrientation p (1 : Fin (3 : ℕ)) orientation) → ((F.slot = a + (2 : Fin
            (3 : ℕ)) → C.1.1.1 = (1 : ℤ) → UnitOccurrenceOrientation p (2 : Fin (3 : ℕ))
            orientation) → ((F.slot ≠ a) → (∀ (t : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple t) → ((t (0 : Fin (4 : ℕ)) = p (2 : Fin (4 : ℕ))) → ((t (1 : Fin
            (4 : ℕ)) = p (3 : Fin (4 : ℕ))) → ((F.slot = a + (2 : Fin (3 : ℕ)) → C.1.1.1 = (1 :
            ℤ) → UnitOccurrenceOrientation t (0 : Fin (3 : ℕ)) orientation) → ((0 < (F.q
            F.slot.succ).1) → (((F.q F.slot.succ).1 < (F.q 0).1) → ((AncestorOdometer (F.q
            F.slot.succ) F.outer.1.1 (D.tiles F.slot false) F.tile (D.functions F.slot false)
            F.odometer) → ((TileOdometer (F.q F.slot.succ) (D.tiles F.slot false) (D.functions
            F.slot false)) → ((∃ (s : ℝ × ℝ), PartialOdometerSlope (D.functions F.slot false) =
            some s) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        (ProperBandQuadruple r) → ((r 1 = C.1.1) → (
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
            (r 0)) → (((BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1
            : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).re + (BandVectors.1 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ)))).re + (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).re = (0 : ℤ)) → (((BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).im +
            (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ)))).im + (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))).im = (0 : ℤ)) → ((BandPrototile (F.q F.slot.succ) (D.tiles F.slot false)) →
            ((FootprintVertices (D.tiles F.slot false) ⊆ FootprintVertices F.tile) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = (if false = true then
            (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (F.slot
            + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) →
            ((TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = -(1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))) -
            (-(GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))))).2,
            (GaussianRealPoint (BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))))).1))) →
            ((TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) → ((-BandVectors.1 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) - BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q
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
            GaussianRealPoint y) → ((
        let y := BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin
            (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))); y ∈ TilingLattice C) → (∀ (u :
            ↥(TilingLattice C)), (Rminus = TileTranslation base (↑u : GaussianInt)) → (
        let join : ProtoTile := TileTranslation base (u + y)
        (join = TileTranslation Rminus y) → ((BandPrototile C.1.1 join) → ((
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
            : ℕ))))) → ((TileCentroid (D.tiles F.slot false) = TileCentroid join) →
            ((BandPrototile C.1.1 (D.tiles F.slot false)) → (((D.tiles F.slot false).cells =
            join.cells ∧ ((D.tiles F.slot false).cells = ∅ → (D.tiles F.slot false).anchor =
            join.anchor)) → ((TileOdometer C.1.1 (TileTranslation base ((↑u : GaussianInt) +
            BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))) (D.functions F.slot false)) →
            ((AncestorOdometer C.1.1 F.outer.1.1 (TileTranslation base ((↑u : GaussianInt) +
            BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin
            (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 :
            Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ))))) F.tile (D.functions F.slot false)
            F.odometer) → ((∀ (c : CircleCoordinates), ∀ (T : ProtoTile), (0 : ℤ) < c.1 →
            BandPrototile c T → Finset.Nonempty T.cells) → (((D.tiles F.slot
            false).cells.Nonempty) → ((join.cells.Nonempty) → ((FootprintVertices
            (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ))))) = FootprintVertices (D.tiles F.slot false)) → ((FootprintVertices
            (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ))))) ⊆ FootprintVertices F.tile) → ((BandSubtileOccurrence F.q F.tile F.slot false
            (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 :
            ℕ)))))) → ((F.q (0 : Fin (4 : ℕ)) = ((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p
            (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1,
            (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 :
            ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2)) →
            ((F.q a.succ = p 0) → ((F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → (∀
            (rootNeg : ℝ × ℝ), ∀ (joinSlope : ℝ × ℝ), (PartialOdometerSlope F.odometer = some
            rootNeg) → ((PartialOdometerSlope (D.functions F.slot false) = some joinSlope) →
            ((joinSlope.1 - rootNeg.1 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ)))).re : ℝ) - (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).im : ℝ))) →
            ((joinSlope.2 - rootNeg.2 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4
            : ℕ)))).im : ℝ) + (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4
            : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))).re : ℝ))) →
            ((rootNeg = F.outerSlope) → ((F.slot = a + (1 : Fin (3 : ℕ))) → (Nonempty
            (P4458T1BoundaryPlacement F
            D))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hp hstep hB hD selected t ht ht0 ht1
      olderChart hCpositive hstrict hselectedAnc hselectedOdo hnegativeSlope r hr hRparent I w x
      y wa xa ya hvsum hasum hvrec harec hvflip haflip hvsumRe hvsumIm hUband hUfoot hUcent
      hUcenter hMcenter hcenterVector hcenterRe hcenterIm hcenter hyLattice u huRminus join
      hjoin_eq hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC hjoinCells hjoinOdo
      hjoinAncestor positiveCells hUnonempty hJoinNonemptyBase hjoinFootEq hjoinFoot
      hjoinOccurrence hq0 hqA hqB hqD rootNeg joinSlope hrootNeg hjoinSlope hjoinSlopeRe
      hjoinSlopeIm hrootNegEq hSB
  have hr1 : r 1 = p 2 := by
    simpa [r, hSB] using hqB
  have hr2 : r 2 = p 3 := SecondNewerRowsGeometry.hr2At377 C orientation base Rminus Rplus
      hminus hplus F a p hqD hSB
  have hr3 : r 3 = p 0 := SecondNewerRowsGeometry.hr3At384 C orientation base Rminus Rplus
      hminus hplus F a p hqA hSB
  have hApos : 0 < (p 0).1 := (ProperBandCurvatureStructure p hp).1
  have hAcoord : F.q a.succ = p 0 := hqA
  have hApos' : 0 < (F.q a.succ).1 := by rw [hAcoord]; exact hApos
  have hAdata := D.slopes a true
  obtain hAzero | ⟨rootSlope, aSlope, hrootSlope, haSlope, hARe, hAIm⟩ := hAdata
  · rw [hAcoord] at hAzero
    omega
  have hrootSlopeEq : rootSlope = F.outerSlope :=
    Option.some.inj (hrootSlope.symm.trans F.slope_outer)
  let directOuter : BandCircle :=
    ⟨⟨p 0, ⟨Or.inl hApos, ⟨p, hp.1, 0, rfl⟩⟩⟩, hApos⟩
  have hparentA : directOuter.1.1 = F.q a.succ := by
    simp [directOuter, hAcoord]
  have hparentB : p 2 = C.1.1 := SecondNewerRowsGeometry.hparentB C orientation base Rminus
      Rplus hminus hplus F a p hqB hSB
  have houterOdo : TileOdometer (p 0) (D.tiles a true) (D.functions a true) := by
    simpa only [hAcoord] using D.odometers a true
  have houterBand : BandPrototile (p 0) (D.tiles a true) :=
    TileOdometerBandPrototile (p 0) (D.tiles a true) (D.functions a true) houterOdo
  have houterAnc := SecondNewerRowsGeometry.houterAnc C orientation base Rminus Rplus hminus
      hplus F D a p hAcoord hApos'
  have hBA : BandVectors.1 (p 2) (p 0) = x := by
    simp [x, hr1, hr3]
  have haBA : BandVectors.2 (p 2) (p 0) = xa := by
    simp [xa, hr1, hr3]
  have hvAB : BandVectors.1 (p 0) (p 2) = I * x := SecondNewerRowsGeometry.hvAB C orientation
      base Rminus Rplus hminus hplus F p hp hBA
  have haAB := SecondNewerRowsGeometry.haAB C orientation base Rminus Rplus hminus hplus F p
      hp haBA
  have hidx2 : Fin.succ (1 : Fin 3) = 2 := by decide
  have hAocc : TileCentroid (D.tiles a true) - TileCentroid F.tile =
      (1 / 2 : ℝ) • (GaussianRealPoint y -
        (-(GaussianRealPoint y).2, (GaussianRealPoint y).1)) :=
            SecondNewerRowsGeometry.hAoccAt427 C orientation base Rminus Rplus hminus hplus F
            D a p hqB hqD hr1 hr2
  have hARe' := SecondNewerRowsGeometry.hARe'At432 C orientation base Rminus Rplus hminus
      hplus F a p hqB hqD hr1 hr2 rootSlope aSlope hARe
  have hAIm' := SecondNewerRowsGeometry.hAIm'At435 C orientation base Rminus Rplus hminus
      hplus F a p hqB hqD hr1 hr2 rootSlope aSlope hAIm
  have hasumRe := BoundaryFrameJoinGeometry.secondVectorSumReal C orientation base Rminus Rplus
      hminus
      hplus F hasum
  have hasumIm := BoundaryFrameJoinGeometry.secondVectorSumImaginary C orientation base Rminus
      Rplus hminus
      hplus F hasum
  have hasumReR : (wa.re : ℝ) + (xa.re : ℝ) + (ya.re : ℝ) = 0 := by
    exact_mod_cast hasumRe
  have hasumImR : (wa.im : ℝ) + (xa.im : ℝ) + (ya.im : ℝ) = 0 := by
    exact_mod_cast hasumIm
  have toRealRe (z : GaussianInt) :
      (GaussianInt.toComplex z).re = (z.re : ℝ) := (GaussianInt.intCast_re z).symm
  have toRealIm (z : GaussianInt) :
      (GaussianInt.toComplex z).im = (z.im : ℝ) := (GaussianInt.intCast_im z).symm
  have hminusSlopeOffset := SecondNewerRowsGeometry.hminusSlopeOffset C orientation base
      Rminus Rplus hminus hplus F p rootNeg joinSlope hjoinSlopeRe hjoinSlopeIm hrootNegEq
      rootSlope aSlope hrootSlopeEq haBA haAB hARe' hAIm' hasumReR hasumImR toRealRe toRealIm
  have hFplusSlope := SecondNewerRowsGeometry.hFplusSlope C orientation base Rminus Rplus
      hminus hplus F rootSlope hrootSlopeEq
  have hFplusRe := SecondNewerRowsGeometry.hFplusRe C orientation base Rminus Rplus hminus
      hplus F rootSlope hFplusSlope
  have hFplusIm := SecondNewerRowsGeometry.hFplusIm C orientation base Rminus Rplus hminus
      hplus F rootSlope hFplusSlope
  have ha10Re := SecondNewerRowsGeometry.ha10ReAt509 C orientation base Rminus Rplus hminus
      hplus F harec
  have ha10Im := SecondNewerRowsGeometry.ha10ImAt513 C orientation base Rminus Rplus hminus
      hplus F harec
  have ha01Re := SecondNewerRowsGeometry.ha01ReAt517 C orientation base Rminus Rplus hminus
      hplus F haflip ha10Im
  have ha01Im := SecondNewerRowsGeometry.ha01ImAt522 C orientation base Rminus Rplus hminus
      hplus F haflip ha10Re
  have hplusReVec := SecondNewerRowsGeometry.hplusReVec C orientation base Rminus Rplus
      hminus hplus F p haBA haAB
  have hplusImVec := SecondNewerRowsGeometry.hplusImVec C orientation base Rminus Rplus
      hminus hplus F p haBA haAB
  have hFplusRe' := SecondNewerRowsGeometry.hFplusRe' C orientation base Rminus Rplus hminus
      hplus F rootSlope toRealRe hFplusRe
  have hFplusIm' := SecondNewerRowsGeometry.hFplusIm' C orientation base Rminus Rplus hminus
      hplus F rootSlope toRealIm hFplusIm
  have hplusSlopeOffset := SecondNewerRowsGeometry.hplusSlopeOffset C orientation base Rminus
      Rplus hminus hplus F p rootSlope aSlope hARe' hAIm' ha10Re ha10Im ha01Re ha01Im
      hplusReVec hplusImVec hFplusRe' hFplusIm'
  have firstParentPlacement : Nonempty (P4458T1BoundaryPlacement F D) :=
      SecondParentPlacements.firstParentPlacement C orientation base Rminus Rplus hminus
      hplus F D a p hp hstep hB hD selected t ht ht0 ht1 olderChart hCpositive hstrict
      hselectedAnc hselectedOdo hnegativeSlope hr hRparent hvsum hasum hvrec harec hvflip
      haflip hvsumRe hvsumIm hUband hUfoot hUcent hUcenter hMcenter hcenterVector hcenterRe
      hcenterIm hcenter hyLattice u huRminus hjoin_eq hjoinBand hjoinFamily hjoinCenter
      hjoinCenterEq hUbandC hjoinCells hjoinOdo hjoinAncestor positiveCells hUnonempty
      hJoinNonemptyBase hjoinFootEq hjoinFoot hjoinOccurrence hq0 hqA hqB hqD rootNeg
      joinSlope hrootNeg hjoinSlope hjoinSlopeRe hjoinSlopeIm hrootNegEq hSB hr1 hr2 hr3
      hApos hAcoord hApos' rootSlope aSlope hrootSlope haSlope hARe hAIm hrootSlopeEq
      hparentA hparentB houterOdo houterBand houterAnc hBA haBA hvAB haAB hidx2 hAocc hARe'
      hAIm' hasumRe hasumIm hasumReR hasumImR hminusSlopeOffset hFplusSlope hFplusRe hFplusIm
      ha10Re ha10Im ha01Re ha01Im hplusReVec hplusImVec hFplusRe' hFplusIm' hplusSlopeOffset
  exact firstParentPlacement

private theorem recursiveParentCase :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), ∀ (a : Fin (3 : ℕ)), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), (ProperBandQuadruple p) → ((F.slot = a + (2 : Fin (3 : ℕ)) →
            C.1.1.1 = (1 : ℤ) → UnitOccurrenceOrientation p (2 : Fin (3 : ℕ)) orientation) → (∀
            (t : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple t) → ((t (0 : Fin (4 :
            ℕ)) = p (2 : Fin (4 : ℕ))) → ((t (1 : Fin (4 : ℕ)) = p (3 : Fin (4 : ℕ))) → ((F.slot
            = a + (2 : Fin (3 : ℕ)) → C.1.1.1 = (1 : ℤ) → UnitOccurrenceOrientation t (0 : Fin (3
            : ℕ)) orientation) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let I : GaussianInt := ⟨0, 1⟩
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa + xa + ya = 0) → ((BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.2 (r 1) (r
            0) = xa + I * ya) → ((BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0)) →
            ((BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0)) → ((TileCentroid Rminus
            - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (r 1) (r 0) -
            BandVectors.1 (r 0) (r 1))) → ((TileCentroid (D.tiles F.slot false) - TileCentroid
            Rminus = GaussianRealPoint y) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (
        let join := TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 :
            ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin
            (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q
            (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4
            : ℕ)))); join ∈ RegularTileFamily base (TilingLattice C)) → ((TileCentroid (D.tiles
            F.slot false) = TileCentroid join) → (((D.tiles F.slot false).cells = join.cells ∧
            ((D.tiles F.slot false).cells = ∅ → (D.tiles F.slot false).anchor = join.anchor)) →
            ((TileOdometer C.1.1 (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))) (D.functions F.slot false)) → ((AncestorOdometer
            C.1.1 F.outer.1.1 (TileTranslation base ((↑u : GaussianInt) + BandVectors.1 (![F.q (0
            : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (1 : Fin (4 : ℕ))))) F.tile (D.functions F.slot false) F.odometer) →
            ((BandSubtileOccurrence F.q F.tile F.slot false (TileTranslation base ((↑u :
            GaussianInt) + BandVectors.1 (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot +
            (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 : ℕ)))
            (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (1 : Fin (4 : ℕ)))))) → ((F.q a.succ = p 0) →
            ((F.q (a + 1).succ = p 2) → ((F.q (a + 2).succ = p 3) → (∀ (rootNeg : ℝ × ℝ), ∀
            (joinSlope : ℝ × ℝ), (PartialOdometerSlope (D.functions F.slot false) = some
            joinSlope) → ((joinSlope.1 - rootNeg.1 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q (0 :
            Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot +
            (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).re : ℝ) - (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ)))).im : ℝ))) → ((joinSlope.2 - rootNeg.2 = -(1 / 2 : ℝ) * ((↑(BandVectors.2 (![F.q
            (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q
            (F.slot + (2 : Fin (3 : ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q
            F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (2 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (![F.q (0 : Fin (4 : ℕ)),
            F.q F.slot.succ, F.q (F.slot + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ] (3 : Fin (4 : ℕ))) (![F.q (0 : Fin (4 : ℕ)), F.q F.slot.succ, F.q (F.slot
            + (1 : Fin (3 : ℕ))).succ, F.q (F.slot + (2 : Fin (3 : ℕ))).succ] (2 : Fin (4 :
            ℕ)))).re : ℝ))) → ((rootNeg = F.outerSlope) → ((F.slot = a + (2 : Fin (3 : ℕ))) →
            (Nonempty (P4458T1BoundaryPlacement F D)))))))))))))))))))))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hp hD t ht ht0 ht1 olderChart r I x
      y wa xa ya hasum hvrec harec hvflip haflip hMcenter hcenter u join hjoinFamily
      hjoinCenterEq hjoinCells hjoinOdo hjoinAncestor hjoinOccurrence hqA hqB hqD rootNeg
      joinSlope hjoinSlope hjoinSlopeRe hjoinSlopeIm hrootNegEq hSD
  have hr1 : r 1 = p 3 := by
    simpa [r, hSD] using hqD
  have hr2 : r 2 = p 0 := SecondNewerRowsGeometry.hr2At770 C orientation base Rminus Rplus
      hminus hplus F a p hqA hSD
  have hr3 : r 3 = p 2 := SecondNewerRowsGeometry.hr3At777 C orientation base Rminus Rplus
      hminus hplus F a p hqB hSD
  have hApos : 0 < (p 0).1 := (ProperBandCurvatureStructure p hp).1
  have hBpos := SecondNewerRowsGeometry.hBpos p t ht ht0
  have hAdata := D.slopes a true
  obtain hAzero | ⟨rootA, slopeA, hrootA, hslopeA, hARe, hAIm⟩ := hAdata
  · rw [hqA] at hAzero
    omega
  have hrootAEq : rootA = F.outerSlope :=
    Option.some.inj (hrootA.symm.trans F.slope_outer)
  have hBdata := D.slopes (a + 1) true
  obtain hBzero | ⟨rootB, slopeB, hrootB, hslopeB, hBRe, hBIm⟩ := hBdata
  · rw [hqB] at hBzero
    omega
  have hrootBEq : rootB = F.outerSlope :=
    Option.some.inj (hrootB.symm.trans F.slope_outer)
  let recursiveOuter : BandCircle :=
    ⟨⟨p 0, ⟨Or.inl hApos, ⟨p, hp.1, 0, rfl⟩⟩⟩, hApos⟩
  have houterA : recursiveOuter.1.1 = F.q a.succ := by
    simp [recursiveOuter, hqA]
  have houterAOdo := SecondNewerRowsGeometry.houterAOdo C orientation base Rminus Rplus
      hminus hplus F D a p hqA
  have houterABand : BandPrototile (p 0) (D.tiles a true) :=
    TileOdometerBandPrototile (p 0) (D.tiles a true)
      (D.functions a true) houterAOdo
  have hparentD : p 3 = C.1.1 := SecondNewerRowsGeometry.hparentD C orientation base Rminus
      Rplus hminus hplus F a p hqD hSD
  have hAocc : TileCentroid (D.tiles a true) - TileCentroid F.tile =
      (1 / 2 : ℝ) • (GaussianRealPoint x -
        (-(GaussianRealPoint x).2, (GaussianRealPoint x).1)) :=
            SecondNewerRowsGeometry.hAoccAt816 C orientation base Rminus Rplus hminus hplus F
            D a p hqB hqD hr1 hr3
  let pRot : Fin 4 → CircleCoordinates := ![p 0, p 3, p 1, p 2]
  have hpRot := SecondNewerRowsGeometry.hpRot p hp
  have hRotV := SecondNewerRowsGeometry.hRotV p hpRot
  have hRotA := SecondNewerRowsGeometry.hRotA p hpRot
  have hRotVReR : ((BandVectors.1 (p 0) (p 3)).re : ℝ) =
      -((BandVectors.1 (p 3) (p 0)).im : ℝ) := by exact_mod_cast
          (SecondNewerRowsGeometry.hRotVRe p hRotV)
  have hRotVImR : ((BandVectors.1 (p 0) (p 3)).im : ℝ) =
      ((BandVectors.1 (p 3) (p 0)).re : ℝ) := by exact_mod_cast
          (SecondNewerRowsGeometry.hRotVIm p hRotV)
  have hrecVReR : ((BandVectors.1 (r 1) (r 0)).re : ℝ) =
      (x.re : ℝ) + (y.im : ℝ) := by exact_mod_cast (SecondNewerRowsGeometry.hrecVRe C
          orientation base Rminus Rplus hminus hplus F hvrec)
  have hrecVImR : ((BandVectors.1 (r 1) (r 0)).im : ℝ) =
      (x.im : ℝ) - (y.re : ℝ) := by exact_mod_cast (SecondNewerRowsGeometry.hrecVIm C
          orientation base Rminus Rplus hminus hplus F hvrec)
  have hflipVReR : ((BandVectors.1 (r 0) (r 1)).re : ℝ) =
      -((BandVectors.1 (r 1) (r 0)).im : ℝ) := by exact_mod_cast
          (SecondNewerRowsGeometry.hflipVRe C orientation base Rminus Rplus hminus hplus F
          hvflip)
  have hflipVImR : ((BandVectors.1 (r 0) (r 1)).im : ℝ) =
      ((BandVectors.1 (r 1) (r 0)).re : ℝ) := by exact_mod_cast
          (SecondNewerRowsGeometry.hflipVIm C orientation base Rminus Rplus hminus hplus F
          hvflip)
  have hyRot : y = BandVectors.1 (p 0) (p 3) := by
    simp [y, hr1, hr2]
  have toRealRe (z : GaussianInt) :
      (GaussianInt.toComplex z).re = (z.re : ℝ) :=
    (GaussianInt.intCast_re z).symm
  have toRealIm (z : GaussianInt) :
      (GaussianInt.toComplex z).im = (z.im : ℝ) :=
    (GaussianInt.intCast_im z).symm
  have hrecVC := SecondNewerRowsGeometry.hrecVC C orientation base Rminus Rplus hminus hplus
      F hvrec
  have hflipVC := SecondNewerRowsGeometry.hflipVC C orientation base Rminus Rplus hminus
      hplus F hvflip
  have hRotVC := SecondNewerRowsGeometry.hRotVC p hRotV
  have hyRotC : GaussianInt.toComplex y =
      GaussianInt.toComplex (BandVectors.1 (p 0) (p 3)) :=
    congrArg GaussianInt.toComplex hyRot
  have hleftAminus := SecondNewerRowsGeometry.hleftAminus C orientation base Rminus Rplus
      hminus hplus F D a p hMcenter hAocc hRotVReR hRotVImR hrecVReR hrecVImR hflipVReR
      hflipVImR hyRot
  have hARe' := SecondNewerRowsGeometry.hARe'At945 C orientation base Rminus Rplus hminus
      hplus F a p hqB hqD hr1 hr3 rootA slopeA hARe
  have hAIm' := SecondNewerRowsGeometry.hAIm'At948 C orientation base Rminus Rplus hminus
      hplus F a p hqB hqD hr1 hr3 rootA slopeA hAIm
  have ha10Re := SecondNewerRowsGeometry.ha10ReAt509 C orientation base Rminus Rplus hminus
      hplus F harec
  have ha10Im := SecondNewerRowsGeometry.ha10ImAt955 C orientation base Rminus Rplus hminus
      hplus F harec
  have ha01Re := SecondNewerRowsGeometry.ha01ReAt959 C orientation base Rminus Rplus hminus
      hplus F haflip ha10Im
  have ha01Im := SecondNewerRowsGeometry.ha01ImAt963 C orientation base Rminus Rplus hminus
      hplus F haflip ha10Re
  have hyaA : ya = BandVectors.2 (p 0) (p 3) := by
    simp [ya, hr1, hr2]
  have ha10ReR : ((BandVectors.2 (r 1) (r 0)).re : ℝ) =
      (xa.re : ℝ) - (ya.im : ℝ) := by exact_mod_cast ha10Re
  have ha10ImR : ((BandVectors.2 (r 1) (r 0)).im : ℝ) =
      (xa.im : ℝ) + (ya.re : ℝ) := by exact_mod_cast ha10Im
  have ha01ReR : ((BandVectors.2 (r 0) (r 1)).re : ℝ) =
      (xa.im : ℝ) + (ya.re : ℝ) := by exact_mod_cast ha01Re
  have ha01ImR : ((BandVectors.2 (r 0) (r 1)).im : ℝ) =
      -(xa.re : ℝ) + (ya.im : ℝ) := by exact_mod_cast ha01Im
  have hRotAReR : ((BandVectors.2 (p 0) (p 3)).re : ℝ) =
      ((BandVectors.2 (p 3) (p 0)).im : ℝ) := by exact_mod_cast
          (SecondNewerRowsGeometry.hRotARe p hRotA)
  have hRotAImR : ((BandVectors.2 (p 0) (p 3)).im : ℝ) =
      -((BandVectors.2 (p 3) (p 0)).re : ℝ) := by exact_mod_cast
          (SecondNewerRowsGeometry.hRotAIm p hRotA)
  have hFminusSlope := SecondNewerRowsGeometry.hFminusSlopeAt991 C orientation base Rminus
      Rplus hminus hplus F rootA hrootAEq
  have hFminusRe := SecondNewerRowsGeometry.hFminusReAt996 C orientation base Rminus Rplus
      hminus hplus F rootA hFminusSlope
  have hFminusIm := SecondNewerRowsGeometry.hFminusImAt1002 C orientation base Rminus Rplus
      hminus hplus F rootA hFminusSlope
  have hrootNegA : rootNeg = rootA := hrootNegEq.trans hrootAEq.symm
  have hasumRe := BoundaryFrameJoinGeometry.secondVectorSumReal C orientation base Rminus Rplus
      hminus hplus F hasum
  have hasumIm := BoundaryFrameJoinGeometry.secondVectorSumImaginary C orientation base Rminus Rplus
      hminus hplus F hasum
  have hasumReR : (wa.re : ℝ) + (xa.re : ℝ) + (ya.re : ℝ) = 0 := by
    exact_mod_cast hasumRe
  have hasumImR : (wa.im : ℝ) + (xa.im : ℝ) + (ya.im : ℝ) = 0 := by
    exact_mod_cast hasumIm
  have secondParentPlacement : Nonempty (P4458T1BoundaryPlacement F D) :=
      SecondParentPlacements.secondParentPlacement C orientation base Rminus Rplus hminus
      hplus F D a p hp hD t ht ht0 ht1 olderChart hvrec hvflip hMcenter hcenter u hjoinFamily
      hjoinCenterEq hjoinCells hjoinOdo hjoinAncestor hjoinOccurrence hqA hqB hqD rootNeg
      joinSlope hjoinSlope hjoinSlopeRe hjoinSlopeIm hrootNegEq hSD hr1 hr2 hr3 hApos hBpos
      rootA slopeA hslopeA rootB slopeB hslopeB hBRe hBIm hrootBEq houterA houterAOdo
      houterABand hparentD toRealRe toRealIm hleftAminus hARe' hAIm' hyaA ha10ReR ha10ImR
      ha01ReR ha01ImR hRotAReR hRotAImR hFminusRe hFminusIm hrootNegA hasumReR hasumImR
  exact secondParentPlacement

end SecondParentCases

theorem P4458T1SecondNewerRows :
    ∀ {C : BandCircle}, ∀ {orientation : Bool}, ∀ {base : ProtoTile}, ∀ {Rminus : ProtoTile}, ∀
        {Rplus : ProtoTile}, ∀ {hminus : PartialOdometer}, ∀ {hplus : PartialOdometer}, ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates),
        (ProperBandQuadruple p) → ((![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3]) → ((F.slot = a + 1 → C.1.1.1 = 1 →
      UnitOccurrenceOrientation p 1 orientation) → ((F.slot = a + 2 → C.1.1.1 = 1 →
      UnitOccurrenceOrientation p 2 orientation) → ((F.slot ≠ a) → (∀ (t : Fin 4 →
          CircleCoordinates), (ProperBandQuadruple t) → ((t 0 = p 2) → ((t 1 = p 3) → (((p 3).1 <
          (p 2).1) → ((F.slot = a + 2 → C.1.1.1 = 1 →
      UnitOccurrenceOrientation t 0 orientation) → (Nonempty (P4458T1BoundaryPlacement F
          D))))))))))) := by
  intro C orientation base Rminus Rplus hminus hplus F D a p hp hstep hB hD selected t ht ht0 ht1
      newer olderChart
-- BODY
  exact (by
    classical
    have hCpositive : 0 < (F.q F.slot.succ).1 := by
      simpa only [← F.parent] using C.2
    have hstrict : (F.q F.slot.succ).1 < (F.q 0).1 := F.proper.2 F.slot
    have hselectedAnc := D.ancestors F.slot false hCpositive
    have hselectedOdo := D.odometers F.slot false
    have hselectedOcc := D.occurrences F.slot false
    have hnegativeSlope := SecondNewerRowsGeometry.hnegativeSlope C orientation base Rminus Rplus
        hminus hplus F D hCpositive
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
        F.q ((F.slot + 2).succ)]
    have hr : ProperBandQuadruple r :=
    BoundaryFrameRowGeometry.presentationProper C orientation base Rminus Rplus
        hminus hplus F
    have hRparent : r 1 = C.1.1 := by simpa [r] using F.parent
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
    have hvflip : BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0) := by
      simpa [I] using (VectorRecursionLaws r hr.1).2.2.2.2 hr 0 |>.1
    have haflip : BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0) := by
      simpa [I] using (VectorRecursionLaws r hr.1).2.2.2.2 hr 0 |>.2
    have hvsumRe := BoundaryFrameJoinGeometry.firstVectorSumReal C orientation base Rminus Rplus
        hminus hplus
        F hvsum
    have hvsumIm := BoundaryFrameJoinGeometry.firstVectorSumImaginary C orientation base Rminus
        Rplus hminus hplus
        F hvsum
    rcases hselectedOcc with ⟨hUband, hUfoot, hUcent⟩
    have hUcenter := BoundaryFrameJoinGeometry.selectedCentroid C orientation base Rminus Rplus
        hminus
        hplus F D hUcent
    have hMcenter : TileCentroid Rminus - TileCentroid F.tile =
        (1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1)) :=
              BoundaryFrameJoinGeometry.minusCentroid C orientation base Rminus Rplus hminus hplus F
    have hcenterVector := (show
        -w + I * w - BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1) = 2 * y
      from by
        classical
        change w.re + x.re + y.re = 0 at hvsumRe
        change w.im + x.im + y.im = 0 at hvsumIm
        rw [hvflip, hvrec]
        apply Zsqrtd.ext <;>
          norm_num [I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> omega)
    have hcenterRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) hcenterVector
    have hcenterIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) hcenterVector
    have hcenter : TileCentroid (D.tiles F.slot false) - TileCentroid Rminus =
        GaussianRealPoint y :=
    BoundaryFrameRowGeometry.centroidDifference C orientation base Rminus Rplus
            hminus hplus F D hUcenter hMcenter hcenterRe hcenterIm
    have hyLattice := SecondNewerRowsGeometry.hyLattice C orientation base Rminus Rplus hminus
        hplus F hr hRparent
    obtain ⟨u, huRminus, _⟩ :=
      RegularTileFamilyTranslationUnique base (TilingLattice C) Rminus F.minus_family
    let join : ProtoTile := TileTranslation base (u + y)
    have translate_add (T : ProtoTile) (v z : GaussianInt) :
        TileTranslation (TileTranslation T v) z = TileTranslation T (v + z) :=
            TileTranslationProperties.add T v z
    have hjoin_eq : join = TileTranslation Rminus y := by
      simpa [join, huRminus] using (translate_add base (u : GaussianInt) y).symm
    have hjoinBand : BandPrototile C.1.1 join := by
      simpa [join] using BandPrototileTranslation C.1.1 base (u + y) F.base_band
    have hjoinFamily := BoundaryFrameJoinGeometry.joinFamily C orientation base Rminus Rplus
        hminus hplus F hyLattice u
    have hjoinCenter := BoundaryFrameJoinGeometry.joinCentroid C orientation base Rminus Rplus
        hminus hplus F u hjoin_eq
    have hjoinCenterEq : TileCentroid (D.tiles F.slot false) = TileCentroid join :=
        BoundaryFrameJoinGeometry.joinCentroidEquality C orientation base Rminus Rplus hminus
            hplus F D
        hcenter u hjoinCenter
    have hUbandC := BoundaryFrameJoinGeometry.parentPrototile C orientation base Rminus Rplus
        hminus hplus
        F D hUband
    have hjoinCells := BandPrototileCentroidUnique C.1.1
      (D.tiles F.slot false) join hUbandC hjoinBand hjoinCenterEq
    have hjoinOdo := SecondNewerRowsGeometry.hjoinOdo C orientation base Rminus Rplus hminus
        hplus F D hselectedOdo u hjoinBand hjoinCells
    have hjoinAncestor := BoundaryFrameJoinGeometry.joinAncestor C orientation base Rminus Rplus
        hminus hplus F D hCpositive hstrict hselectedAnc u hjoinBand hjoinCells
    have positiveCells := BandPrototileNonempty.positive
    have hUnonempty : (D.tiles F.slot false).cells.Nonempty :=
      positiveCells _ _ hCpositive hUband
    have hJoinNonemptyBase : join.cells.Nonempty := by rw [← hjoinCells.1]; exact hUnonempty
    have hjoinFootEq := SecondNewerRowsGeometry.hjoinFootEq C orientation base Rminus Rplus
        hminus hplus F D u hjoinCells hUnonempty hJoinNonemptyBase
    have hjoinFoot := BoundaryFrameJoinGeometry.joinFootprint C orientation base Rminus Rplus hminus
        hplus F D hUfoot u hjoinFootEq
    have hjoinOccurrence := BoundaryFrameJoinGeometry.joinOccurrence C orientation base Rminus
        Rplus hminus hplus F D hUcent u hjoinBand hjoinCenterEq hjoinFoot
    have hq0 := SecondNewerRowsGeometry.hq0 C orientation base Rminus Rplus hminus hplus F a p hstep
    have hqA : F.q a.succ = p 0 := SecondNewerRowsGeometry.hqA C orientation base Rminus Rplus
        hminus hplus F a p hstep
    have hqB : F.q (a + 1).succ = p 2 := SecondNewerRowsGeometry.hqB C orientation base Rminus
        Rplus hminus hplus F a p hstep
    have hqD : F.q (a + 2).succ = p 3 := SecondNewerRowsGeometry.hqD C orientation base Rminus
        Rplus hminus hplus F a p hstep
    have hslot := SecondNewerRowsGeometry.hslot C orientation base Rminus Rplus hminus hplus F a
        p selected
    have hSlopeInfo := SecondNewerRowsGeometry.hSlopeInfo C orientation base Rminus Rplus hminus
        hplus F D hCpositive
    obtain ⟨rootNeg, joinSlope, hrootNeg, hjoinSlope,
      hjoinSlopeRe, hjoinSlopeIm⟩ := hSlopeInfo
    have hrootNegEq : rootNeg = F.outerSlope :=
      Option.some.inj (hrootNeg.symm.trans F.slope_outer)
    rcases hslot with hSB | hSD
    · have directParentCase : Nonempty (P4458T1BoundaryPlacement F D) :=
        SecondParentCases.directParentCase C orientation base Rminus Rplus hminus hplus F D a p
        hp hstep hB hD selected t ht ht0 ht1 olderChart hCpositive hstrict hselectedAnc
        hselectedOdo hnegativeSlope hr hRparent hvsum hasum hvrec harec hvflip haflip hvsumRe
        hvsumIm hUband hUfoot hUcent hUcenter hMcenter hcenterVector hcenterRe hcenterIm hcenter
        hyLattice u huRminus hjoin_eq hjoinBand hjoinFamily hjoinCenter hjoinCenterEq hUbandC
        hjoinCells hjoinOdo hjoinAncestor positiveCells hUnonempty hJoinNonemptyBase hjoinFootEq
        hjoinFoot hjoinOccurrence hq0 hqA hqB hqD rootNeg joinSlope hrootNeg hjoinSlope
        hjoinSlopeRe hjoinSlopeIm hrootNegEq hSB
      exact directParentCase
    · have recursiveParentCase : Nonempty (P4458T1BoundaryPlacement F D) :=
        SecondParentCases.recursiveParentCase C orientation base Rminus Rplus hminus hplus F D a
        p hp hD t ht ht0 ht1 olderChart hasum hvrec harec hvflip haflip hMcenter hcenter u
        hjoinFamily hjoinCenterEq hjoinCells hjoinOdo hjoinAncestor hjoinOccurrence hqA hqB hqD
        rootNeg joinSlope hjoinSlope hjoinSlopeRe hjoinSlopeIm hrootNegEq hSD
      exact recursiveParentCase
  )

end ApollonianSuperharmonic

end
