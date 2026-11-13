/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.P4536T1EndpointAlgebra
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4536T1AFrameD]

/-!
# P4536T1AFrameD

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FrameDiagonalProof

private theorem hrAt128 :
    ∀ (C : BandCircle),
      ∀ (orientation : Bool),
        ∀ (base : ProtoTile),
          ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile),
              ∀ (hminus : PartialOdometer),
                ∀ (hplus : PartialOdometer),
                  ∀ (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
                    ∀ (a : Fin 3),
                      F.slot = a + 2 →
                        let r : Fin 4 → CircleCoordinates :=
                          ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
                        ProperBandQuadruple r := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a hslot r
  fin_cases a
  · have heq : r = F.q := by
      funext j
      fin_cases j <;> rfl
    rw [heq]
    exact F.proper
  · refine ⟨SemiProperQuadruple.rotate F.proper.1, ?_⟩
    have heq : r = ![F.q 0, F.q 2, F.q 3, F.q 1] := by
      funext k
      fin_cases k <;> rfl
    rw [heq]
    intro j
    fin_cases j
    · exact F.proper.2 1
    · exact F.proper.2 2
    · exact F.proper.2 0
  · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate F.proper.1), ?_⟩
    have heq : r = ![F.q 0, F.q 3, F.q 1, F.q 2] := by
      funext k
      fin_cases k <;> rfl
    rw [heq]
    intro j
    fin_cases j
    · exact F.proper.2 2
    · exact F.proper.2 0
    · exact F.proper.2 1

private theorem hrstep :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
        ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
        3).2 - (p 1).2), p 0, p 2, p 3]) → (
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    r = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
      2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p 3]) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep r
  simpa [r] using hstep

private theorem r1 :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
        3).2 - (p 1).2), p 0, p 2, p 3]) → (r 1 = p 0) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r hrstep
  simpa using congrFun hrstep 1

private theorem r2 :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
        3).2 - (p 1).2), p 0, p 2, p 3]) → (r 2 = p 2) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r hrstep
  simpa using congrFun hrstep 2

private theorem r3 :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
        3).2 - (p 1).2), p 0, p 2, p 3]) → (r 3 = p 3) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r hrstep
  simpa using congrFun hrstep 3

private theorem hparent :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
        ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
        3).2 - (p 1).2), p 0, p 2, p 3]) → ((F.slot = a + 2) → (F.q (F.slot).succ = p 3)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep hslot
  have hqE : F.q (a + 2).succ = p 3 := by
    have h := congrFun hstep 3
    simpa using h
  rw [hslot]
  exact hqE

private theorem hparentR :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 3 = p 3) → ((F.q (F.slot).succ = p 3) → (F.q F.slot.succ = r 3)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r r3 hparent
  exact hparent.trans r3.symm

private theorem hzero :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    F.q 0 = r 0 := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r
  exact rfl

private theorem hC :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (p : Fin 4 →
        CircleCoordinates), (F.q (F.slot).succ = p 3) → (C.1.1 = p 3) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F p hparent
  exact F.parent.symm.trans hparent

private theorem positiveA :
    ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (0 < (p 0).1) := by
  classical
  intro p hp
  exact (ProperBandCurvatureStructure p hp).1

private theorem positiveE :
    ∀ (C : BandCircle), ∀ (p : Fin 4 → CircleCoordinates), (C.1.1 = p 3) → (0 < (p 3).1) := by
  classical
  intro C p hC
  rw [← hC]
  exact C.2

private theorem laws :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) +
      BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
    (0 : GaussianInt) ∧
  BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
          BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) +
        BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
      (0 : GaussianInt) ∧
    BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) =
        BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) -
          { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
              ℕ))) ∧
      BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) =
          BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) +
            { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4
                : ℕ))) ∧
        (ProperBandQuadruple r →
          ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ))) (r j.succ) =
                { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
              BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) =
                -{ re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.2 (r j.succ) (r (0 : Fin (4 :
                    ℕ))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hr
  exact VectorRecursionLaws r hr.1

private theorem hrr :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → (
    let rr : Fin 4 → CircleCoordinates := ![r 0, r 3, r 1, r 2]
    ProperBandQuadruple rr) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hr rr
  have hrot := SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hr.1)
  refine ⟨hrot, ?_⟩
  intro j
  fin_cases j
  · simpa [rr] using hr.2 2
  · simpa [rr] using hr.2 0
  · simpa [rr] using hr.2 1

private theorem lawsR :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let rr : Fin 4 → CircleCoordinates := ![r 0, r 3, r 1, r 2]
    (ProperBandQuadruple rr) → (BandVectors.1 (rr (3 : Fin (4 : ℕ))) (rr (2 : Fin (4 : ℕ))) +
        BandVectors.1 (rr (1 : Fin (4 : ℕ))) (rr (3 : Fin (4 : ℕ))) +
      BandVectors.1 (rr (2 : Fin (4 : ℕ))) (rr (1 : Fin (4 : ℕ))) =
    (0 : GaussianInt) ∧
  BandVectors.2 (rr (3 : Fin (4 : ℕ))) (rr (2 : Fin (4 : ℕ))) +
          BandVectors.2 (rr (1 : Fin (4 : ℕ))) (rr (3 : Fin (4 : ℕ))) +
        BandVectors.2 (rr (2 : Fin (4 : ℕ))) (rr (1 : Fin (4 : ℕ))) =
      (0 : GaussianInt) ∧
    BandVectors.1 (rr (1 : Fin (4 : ℕ))) (rr (0 : Fin (4 : ℕ))) =
        BandVectors.1 (rr (1 : Fin (4 : ℕ))) (rr (3 : Fin (4 : ℕ))) -
          { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.1 (rr (2 : Fin (4 : ℕ))) (rr (1 : Fin (4
              : ℕ))) ∧
      BandVectors.2 (rr (1 : Fin (4 : ℕ))) (rr (0 : Fin (4 : ℕ))) =
          BandVectors.2 (rr (1 : Fin (4 : ℕ))) (rr (3 : Fin (4 : ℕ))) +
            { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.2 (rr (2 : Fin (4 : ℕ))) (rr (1 : Fin
                (4 : ℕ))) ∧
        (ProperBandQuadruple rr →
          ∀ (j : Fin (3 : ℕ)), BandVectors.1 (rr (0 : Fin (4 : ℕ))) (rr j.succ) =
                { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.1 (rr j.succ) (rr (0 : Fin (4 :
                    ℕ))) ∧
              BandVectors.2 (rr (0 : Fin (4 : ℕ))) (rr j.succ) =
                -{ re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.2 (rr j.succ) (rr (0 : Fin (4 :
                    ℕ))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r rr hrr
  exact VectorRecursionLaws rr hrr.1

private theorem win :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wv := BandVectors.1 (r 3) (r 2)
    let xv := BandVectors.1 (r 1) (r 3)
    let rr : Fin 4 → CircleCoordinates := ![r 0, r 3, r 1, r 2]
    (BandVectors.1 (rr (3 : Fin (4 : ℕ))) (rr (2 : Fin (4 : ℕ))) + BandVectors.1 (rr (1 : Fin (4
        : ℕ))) (rr (3 : Fin (4 : ℕ))) + BandVectors.1 (rr (2 : Fin (4 : ℕ))) (rr (1 : Fin (4 :
        ℕ))) = (0 : GaussianInt) ∧ BandVectors.2 (rr (3 : Fin (4 : ℕ))) (rr (2 : Fin (4 : ℕ))) +
        BandVectors.2 (rr (1 : Fin (4 : ℕ))) (rr (3 : Fin (4 : ℕ))) + BandVectors.2 (rr (2 : Fin
        (4 : ℕ))) (rr (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (rr (1 : Fin (4 :
        ℕ))) (rr (0 : Fin (4 : ℕ))) = BandVectors.1 (rr (1 : Fin (4 : ℕ))) (rr (3 : Fin (4 : ℕ)))
        - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (rr (2 : Fin (4 : ℕ))) (rr (1 : Fin (4 : ℕ))) ∧
        BandVectors.2 (rr (1 : Fin (4 : ℕ))) (rr (0 : Fin (4 : ℕ))) = BandVectors.2 (rr (1 : Fin
        (4 : ℕ))) (rr (3 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (rr (2 : Fin (4 :
        ℕ))) (rr (1 : Fin (4 : ℕ))) ∧ (ProperBandQuadruple rr → ∀ (j : Fin (3 : ℕ)),
        BandVectors.1 (rr (0 : Fin (4 : ℕ))) (rr j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (rr
        j.succ) (rr (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (rr (0 : Fin (4 : ℕ))) (rr j.succ) = -⟨(0
        : ℤ), (1 : ℤ)⟩ * BandVectors.2 (rr j.succ) (rr (0 : Fin (4 : ℕ))))) → (BandVectors.1 (r
        3) (r 0) = wv - I * xv) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wv xv rr lawsR
  simpa [rr, wv, xv, I] using lawsR.2.2.1

private theorem ain :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let rr : Fin 4 → CircleCoordinates := ![r 0, r 3, r 1, r 2]
    (BandVectors.1 (rr (3 : Fin (4 : ℕ))) (rr (2 : Fin (4 : ℕ))) + BandVectors.1 (rr (1 : Fin (4
        : ℕ))) (rr (3 : Fin (4 : ℕ))) + BandVectors.1 (rr (2 : Fin (4 : ℕ))) (rr (1 : Fin (4 :
        ℕ))) = (0 : GaussianInt) ∧ BandVectors.2 (rr (3 : Fin (4 : ℕ))) (rr (2 : Fin (4 : ℕ))) +
        BandVectors.2 (rr (1 : Fin (4 : ℕ))) (rr (3 : Fin (4 : ℕ))) + BandVectors.2 (rr (2 : Fin
        (4 : ℕ))) (rr (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (rr (1 : Fin (4 :
        ℕ))) (rr (0 : Fin (4 : ℕ))) = BandVectors.1 (rr (1 : Fin (4 : ℕ))) (rr (3 : Fin (4 : ℕ)))
        - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (rr (2 : Fin (4 : ℕ))) (rr (1 : Fin (4 : ℕ))) ∧
        BandVectors.2 (rr (1 : Fin (4 : ℕ))) (rr (0 : Fin (4 : ℕ))) = BandVectors.2 (rr (1 : Fin
        (4 : ℕ))) (rr (3 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (rr (2 : Fin (4 :
        ℕ))) (rr (1 : Fin (4 : ℕ))) ∧ (ProperBandQuadruple rr → ∀ (j : Fin (3 : ℕ)),
        BandVectors.1 (rr (0 : Fin (4 : ℕ))) (rr j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (rr
        j.succ) (rr (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (rr (0 : Fin (4 : ℕ))) (rr j.succ) = -⟨(0
        : ℤ), (1 : ℤ)⟩ * BandVectors.2 (rr j.succ) (rr (0 : Fin (4 : ℕ))))) → (BandVectors.2 (r
        3) (r 0) = wa + I * xa) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa xa rr lawsR
  simpa [rr, wa, xa, I] using lawsR.2.2.2.1

private theorem hv :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wv := BandVectors.1 (r 3) (r 2)
    let xv := BandVectors.1 (r 1) (r 3)
    let yv := BandVectors.1 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → (-(wv - I * wv) - (xv - I * yv - I * (xv - I * yv)) =
        (2 : GaussianInt) * yv ∧
  xv - I * yv + I * (xv - I * yv) + (wv - I * wv) = (2 : GaussianInt) * I * xv ∧
    -(xv - I * xv) - (wv - I * wv) = yv - I * yv ∧
      yv - I * wv + I * (yv - I * wv) - (wv - I * wv) = yv + I * yv ∧
        wv - I * xv - I * (wv - I * xv) - (wv - I * wv) = -I * xv - xv ∧
          -(yv - I * yv) - (wv - I * wv) = -I * xv + xv ∧
            yv - I * wv - I * (yv - I * wv) - (yv - I * yv) = -I * wv - wv ∧
              -(xv - I * xv) - (yv - I * yv) = -I * wv + wv ∧
                -(yv - I * yv) - (xv - I * xv) = wv - I * wv ∧
                  wv - I * xv + I * (wv - I * xv) - (xv - I * xv) = wv + I * wv) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wv xv yv laws
  exact P4536T1EndpointAlgebra I wv xv yv (by decide +kernel) laws.1

private theorem ha :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → (-(wa - -I * wa) - (xa - -I * ya - -I * (xa - -I * ya))
        = (2 : GaussianInt) * ya ∧
  xa - -I * ya + -I * (xa - -I * ya) + (wa - -I * wa) = (2 : GaussianInt) * -I * xa ∧
    -(xa - -I * xa) - (wa - -I * wa) = ya - -I * ya ∧
      ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) = ya + -I * ya ∧
        wa - -I * xa - -I * (wa - -I * xa) - (wa - -I * wa) = - -I * xa - xa ∧
          -(ya - -I * ya) - (wa - -I * wa) = - -I * xa + xa ∧
            ya - -I * wa - -I * (ya - -I * wa) - (ya - -I * ya) = - -I * wa - wa ∧
              -(xa - -I * xa) - (ya - -I * ya) = - -I * wa + wa ∧
                -(ya - -I * ya) - (xa - -I * xa) = wa - -I * wa ∧
                  wa - -I * xa + -I * (wa - -I * xa) - (xa - -I * xa) = wa + -I * wa) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa xa ya laws
  exact P4536T1EndpointAlgebra (-I) wa xa ya (by decide +kernel) laws.2.1

private theorem vflip :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → ((BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r
        (2 : Fin (4 : ℕ))) + BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) +
        BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4
        : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ)))
        (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) =
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ (ProperBandQuadruple r → ∀ (j
        : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ))) (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (r (0 : Fin (4 : ℕ))) (r
        j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r j.succ) (r (0 : Fin (4 : ℕ))))) →
        (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (Fin.succ (2 : Fin (3 : ℕ)))) =
    { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.1 (r (Fin.succ (2 : Fin (3 : ℕ)))) (r (0 : Fin
        (4 : ℕ))) ∧
  BandVectors.2 (r (0 : Fin (4 : ℕ))) (r (Fin.succ (2 : Fin (3 : ℕ)))) =
    -{ re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.2 (r (Fin.succ (2 : Fin (3 : ℕ)))) (r (0 :
        Fin (4 : ℕ))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hr laws
  exact (laws.2.2.2.2 hr) 2

private theorem vflip' :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (Fin.succ (2 : Fin (3 : ℕ)))) = ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (r (Fin.succ (2 : Fin (3 : ℕ)))) (r (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (r
        (0 : Fin (4 : ℕ))) (r (Fin.succ (2 : Fin (3 : ℕ)))) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2
        (r (Fin.succ (2 : Fin (3 : ℕ)))) (r (0 : Fin (4 : ℕ)))) → (BandVectors.1 (r 0) (r 3) = I
        * BandVectors.1 (r 3) (r 0)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I vflip
  simpa using vflip.1

private theorem aflip' :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    (BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (Fin.succ (2 : Fin (3 : ℕ)))) = ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (r (Fin.succ (2 : Fin (3 : ℕ)))) (r (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (r
        (0 : Fin (4 : ℕ))) (r (Fin.succ (2 : Fin (3 : ℕ)))) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2
        (r (Fin.succ (2 : Fin (3 : ℕ)))) (r (0 : Fin (4 : ℕ)))) → (BandVectors.2 (r 0) (r 3) = -I
        * BandVectors.2 (r 3) (r 0)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I aflip
  simpa using aflip.2

private theorem centMinus :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 3 = p 3) → ((F.q (F.slot).succ = p 3) → ((F.q 0 = r 0) → (
    let I : GaussianInt := ⟨0, 1⟩
    let wv := BandVectors.1 (r 3) (r 2)
    let xv := BandVectors.1 (r 1) (r 3)
    (BandVectors.1 (r 3) (r 0) = wv - I * xv) → ((BandVectors.1 (r 0) (r 3) = I * BandVectors.1
        (r 3) (r 0)) → (TileCentroid Rminus - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint ((wv - I * xv) - I * (wv - I * xv))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r r3 hparent hzero I wv xv win vflip'
  have h := F.minus_centroid
  have hindex : F.q F.slot.succ = r 3 := hparent.trans r3.symm
  change TileCentroid Rminus - TileCentroid F.tile =
    (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.1 (F.q F.slot.succ) (F.q 0) - BandVectors.1 (F.q 0) (F.q F.slot.succ)) at h
  rw [hindex, hzero] at h
  rw [vflip', win] at h
  simpa using h

private theorem centJ :
    ∀ (C : BandCircle),
      ∀ (orientation : Bool),
        ∀ (base : ProtoTile),
          ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile),
              ∀ (hminus : PartialOdometer),
                ∀ (hplus : PartialOdometer),
                  ∀
                    (F :
                      P4458T1BoundaryFrame C orientation base Rminus Rplus hminus
                        hplus),
                    ∀ (D : P4458T1RestrictionFamily F),
                      ∀ (a : Fin 3),
                        ((F.slot = a + 2) →
                          (∀ (J : ProtoTile),
                            (TileCentroid J = TileCentroid (D.tiles F.slot false)) →
                              (let r : Fin 4 → CircleCoordinates :=
                                ![F.q 0, F.q a.succ, F.q (a + 1).succ,
                                  F.q (a + 2).succ];
                              (let I : GaussianInt := ⟨0, 1⟩;
                              let yv := BandVectors.1 (r 2) (r 1);
                              (TileCentroid J - TileCentroid F.tile =
                                (1 / 2 : ℝ) •
                                  GaussianRealPoint (-(yv - I * yv))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a hslot J hcent r I yv
  have h := (D.occurrences F.slot false).2.2
  have hs2 : F.slot + 2 = a + 1 := by
    rw [hslot]
    fin_cases a <;> decide
  have hs1 : F.slot + 1 = a := by
    rw [hslot]
    fin_cases a <;> decide
  have hindices : F.q ((F.slot + 2).succ) = r 2 ∧ F.q ((F.slot + 1).succ) = r 1 := by
    rw [hs2, hs1]
    constructor <;> rfl
  change TileCentroid (D.tiles F.slot false) - TileCentroid F.tile =
    (-1 : ℝ) • ((1 / 2 : ℝ) •
      (GaussianRealPoint (BandVectors.1 (F.q ((F.slot + 2).succ)) (F.q ((F.slot + 1).succ)) ) -
        (-(GaussianRealPoint (BandVectors.1 (F.q ((F.slot + 2).succ)) (F.q ((F.slot + 1).succ)))).2,
          (GaussianRealPoint (BandVectors.1 (F.q ((F.slot + 2).succ)) (F.q ((F.slot +
              1).succ)))).1))) at h
  rw [hindices.1, hindices.2] at h
  rw [hcent]
  rw [h]
  ext <;> simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

private theorem centK :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wv := BandVectors.1 (r 3) (r 2)
    TileCentroid (D.tiles a true) - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint (wv - I * wv) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a r I wv
  have h := (D.occurrences a true).2.2
  have hindices : F.q ((a + 2).succ) = r 3 ∧ F.q ((a + 1).succ) = r 2 := by
    constructor <;> rfl
  change TileCentroid (D.tiles a true) - TileCentroid F.tile =
    (1 : ℝ) • ((1 / 2 : ℝ) •
      (GaussianRealPoint (BandVectors.1 (F.q ((a + 2).succ)) (F.q ((a + 1).succ))) -
        (-(GaussianRealPoint (BandVectors.1 (F.q ((a + 2).succ)) (F.q ((a + 1).succ)))).2,
          (GaussianRealPoint (BandVectors.1 (F.q ((a + 2).succ)) (F.q ((a + 1).succ)))).1))) at h
  rw [hindices.1, hindices.2] at h
  rw [h]
  ext <;> simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

private theorem halfDiff :
    ∀ {X : GaussianInt}, ∀ {Y : GaussianInt}, ∀ {Z : GaussianInt}, (X - Y = Z) → ((1 / 2 : ℝ) •
        GaussianRealPoint X -
        (1 / 2 : ℝ) • GaussianRealPoint Y =
          (1 / 2 : ℝ) • GaussianRealPoint Z) := by
  classical
  intro X Y Z hxy
  have hr := congrArg (fun z : GaussianInt => z.re) hxy
  have hi := congrArg (fun z : GaussianInt => z.im) hxy
  have hr' : (X.re : ℝ) - (Y.re : ℝ) = (Z.re : ℝ) := by exact_mod_cast (by simpa using hr)
  have hi' : (X.im : ℝ) - (Y.im : ℝ) = (Z.im : ℝ) := by exact_mod_cast (by simpa using hi)
  apply Prod.ext
  · change (1 / 2 : ℝ) * (X.re : ℝ) - (1 / 2 : ℝ) * (Y.re : ℝ) =
      (1 / 2 : ℝ) * (Z.re : ℝ)
    linarith
  · change (1 / 2 : ℝ) * (X.im : ℝ) - (1 / 2 : ℝ) * (Y.im : ℝ) =
      (1 / 2 : ℝ) * (Z.im : ℝ)
    linarith

private theorem hcentR :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wv := BandVectors.1 (r 3) (r 2)
    let xv := BandVectors.1 (r 1) (r 3)
    let yv := BandVectors.1 (r 2) (r 1)
    (-(wv - I * wv) - (xv - I * yv - I * (xv - I * yv)) = (2 : GaussianInt) * yv ∧ xv - I * yv +
        I * (xv - I * yv) + (wv - I * wv) = (2 : GaussianInt) * I * xv ∧ -(xv - I * xv) - (wv - I
        * wv) = yv - I * yv ∧ yv - I * wv + I * (yv - I * wv) - (wv - I * wv) = yv + I * yv ∧ wv
        - I * xv - I * (wv - I * xv) - (wv - I * wv) = -I * xv - xv ∧ -(yv - I * yv) - (wv - I *
        wv) = -I * xv + xv ∧ yv - I * wv - I * (yv - I * wv) - (yv - I * yv) = -I * wv - wv ∧
        -(xv - I * xv) - (yv - I * yv) = -I * wv + wv ∧ -(yv - I * yv) - (xv - I * xv) = wv - I *
        wv ∧ wv - I * xv + I * (wv - I * xv) - (xv - I * xv) = wv + I * wv) → ((TileCentroid
        Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint ((wv - I * xv) - I * (wv -
        I * xv))) → ((TileCentroid (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) •
        GaussianRealPoint (wv - I * wv)) → ((∀ {X : GaussianInt}, ∀ {Y : GaussianInt}, ∀
        {Z : GaussianInt}, (X - Y = Z) → ((1 / 2 : ℝ) • GaussianRealPoint X - (1 / 2 : ℝ) •
        GaussianRealPoint Y = (1 / 2 : ℝ) • GaussianRealPoint Z)) → (TileCentroid Rminus -
        TileCentroid (D.tiles a true) =
      (1 / 2 : ℝ) • GaussianRealPoint (-I * xv - xv))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a r I wv xv yv hv centMinus centK halfDiff
  calc
    _ = (TileCentroid Rminus - TileCentroid F.tile) -
        (TileCentroid (D.tiles a true) - TileCentroid F.tile) := by abel
    _ = _ := by rw [centMinus, centK]; exact halfDiff hv.2.2.2.2.1

private theorem hcentJ :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (J : ProtoTile),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wv := BandVectors.1 (r 3) (r 2)
    let xv := BandVectors.1 (r 1) (r 3)
    let yv := BandVectors.1 (r 2) (r 1)
    (-(wv - I * wv) - (xv - I * yv - I * (xv - I * yv)) = (2 : GaussianInt) * yv ∧ xv - I * yv +
        I * (xv - I * yv) + (wv - I * wv) = (2 : GaussianInt) * I * xv ∧ -(xv - I * xv) - (wv - I
        * wv) = yv - I * yv ∧ yv - I * wv + I * (yv - I * wv) - (wv - I * wv) = yv + I * yv ∧ wv
        - I * xv - I * (wv - I * xv) - (wv - I * wv) = -I * xv - xv ∧ -(yv - I * yv) - (wv - I *
        wv) = -I * xv + xv ∧ yv - I * wv - I * (yv - I * wv) - (yv - I * yv) = -I * wv - wv ∧
        -(xv - I * xv) - (yv - I * yv) = -I * wv + wv ∧ -(yv - I * yv) - (xv - I * xv) = wv - I *
        wv ∧ wv - I * xv + I * (wv - I * xv) - (xv - I * xv) = wv + I * wv) → ((TileCentroid J -
        TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (-(yv - I * yv))) → ((TileCentroid
        (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (wv - I * wv)) →
        ((∀ {X : GaussianInt}, ∀ {Y : GaussianInt}, ∀ {Z : GaussianInt}, (X - Y = Z) → ((1 / 2 :
        ℝ) • GaussianRealPoint X - (1 / 2 : ℝ) • GaussianRealPoint Y = (1 / 2 : ℝ) •
        GaussianRealPoint Z)) → (TileCentroid J - TileCentroid (D.tiles a true) =
      (1 / 2 : ℝ) • GaussianRealPoint (-I * xv + xv))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a J r I wv xv yv hv centJ centK halfDiff
  calc
    _ = (TileCentroid J - TileCentroid F.tile) -
        (TileCentroid (D.tiles a true) - TileCentroid F.tile) := by abel
    _ = _ := by rw [centJ, centK]; exact halfDiff hv.2.2.2.2.2.1

private theorem lawsP :
    ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (BandVectors.1 (p (3 : Fin (4 :
        ℕ))) (p (2 : Fin (4 : ℕ))) + BandVectors.1 (p (1 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) +
      BandVectors.1 (p (2 : Fin (4 : ℕ))) (p (1 : Fin (4 : ℕ))) =
    (0 : GaussianInt) ∧
  BandVectors.2 (p (3 : Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ))) +
          BandVectors.2 (p (1 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) +
        BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (1 : Fin (4 : ℕ))) =
      (0 : GaussianInt) ∧
    BandVectors.1 (p (1 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) =
        BandVectors.1 (p (1 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) -
          { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.1 (p (2 : Fin (4 : ℕ))) (p (1 : Fin (4 :
              ℕ))) ∧
      BandVectors.2 (p (1 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) =
          BandVectors.2 (p (1 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) +
            { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (1 : Fin (4
                : ℕ))) ∧
        (ProperBandQuadruple p →
          ∀ (j : Fin (3 : ℕ)), BandVectors.1 (p (0 : Fin (4 : ℕ))) (p j.succ) =
                { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.1 (p j.succ) (p (0 : Fin (4 : ℕ))) ∧
              BandVectors.2 (p (0 : Fin (4 : ℕ))) (p j.succ) =
                -{ re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.2 (p j.succ) (p (0 : Fin (4 :
                    ℕ))))) := by
  classical
  intro p hp
  exact VectorRecursionLaws p hp.1

private theorem pflip :
    ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → ((BandVectors.1 (p (3 : Fin (4 :
        ℕ))) (p (2 : Fin (4 : ℕ))) + BandVectors.1 (p (1 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) +
        BandVectors.1 (p (2 : Fin (4 : ℕ))) (p (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.2 (p (3 : Fin (4 : ℕ))) (p (2 : Fin (4 : ℕ))) + BandVectors.2 (p (1 : Fin (4
        : ℕ))) (p (3 : Fin (4 : ℕ))) + BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (1 : Fin (4 : ℕ)))
        = (0 : GaussianInt) ∧ BandVectors.1 (p (1 : Fin (4 : ℕ))) (p (0 : Fin (4 : ℕ))) =
        BandVectors.1 (p (1 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (p (2 : Fin (4 : ℕ))) (p (1 : Fin (4 : ℕ))) ∧ BandVectors.2 (p (1 : Fin (4
        : ℕ))) (p (0 : Fin (4 : ℕ))) = BandVectors.2 (p (1 : Fin (4 : ℕ))) (p (3 : Fin (4 : ℕ)))
        + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (p (2 : Fin (4 : ℕ))) (p (1 : Fin (4 : ℕ))) ∧
        (ProperBandQuadruple p → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (p (0 : Fin (4 : ℕ))) (p
        j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (p j.succ) (p (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (p (0 : Fin (4 : ℕ))) (p j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (p
        j.succ) (p (0 : Fin (4 : ℕ))))) → (BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (Fin.succ (2 :
        Fin (3 : ℕ)))) =
    { re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.1 (p (Fin.succ (2 : Fin (3 : ℕ)))) (p (0 : Fin
        (4 : ℕ))) ∧
  BandVectors.2 (p (0 : Fin (4 : ℕ))) (p (Fin.succ (2 : Fin (3 : ℕ)))) =
    -{ re := (0 : ℤ), im := (1 : ℤ) } * BandVectors.2 (p (Fin.succ (2 : Fin (3 : ℕ)))) (p (0 :
        Fin (4 : ℕ))))) := by
  classical
  intro p hp lawsP
  exact (lawsP.2.2.2.2 hp) 2

private theorem hxcoordV :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 1 = p 0) → ((r 3 = p 3) → (
    let xv := BandVectors.1 (r 1) (r 3)
    BandVectors.1 (p 0) (p 3) = xv)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r r1 r3 xv
  rw [← r1, ← r3]

private theorem hxcoordA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 1 = p 0) → ((r 3 = p 3) → (
    let xa := BandVectors.2 (r 1) (r 3)
    BandVectors.2 (p 0) (p 3) = xa)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r r1 r3 xa
  rw [← r1, ← r3]

private theorem hI2 :
    let I : GaussianInt := ⟨0, 1⟩
    I * I = -1 := by
  classical
  intro I
  decide +kernel

private theorem he2 :
    let I : GaussianInt := ⟨0, 1⟩
    let e : GaussianInt := -I
    e * e = -1 := by
  classical
  intro I e
  decide +kernel

private theorem hIneg :
    let I : GaussianInt := ⟨0, 1⟩
    (I * I = -1) → (-I * I = 1) := by
  classical
  intro I hI2
  calc
    -I * I = -(I * I) := by ring
    _ = -(-1) := by rw [hI2]
    _ = 1 := by norm_num

private theorem heneg :
    let I : GaussianInt := ⟨0, 1⟩
    let e : GaussianInt := -I
    (e * e = -1) → (-e * e = 1) := by
  classical
  intro I e he2
  calc
    -e * e = -(e * e) := by ring
    _ = -(-1) := by rw [he2]
    _ = 1 := by norm_num

private theorem hxv :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xv := BandVectors.1 (r 1) (r 3)
    (BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (Fin.succ (2 : Fin (3 : ℕ)))) = ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (p (Fin.succ (2 : Fin (3 : ℕ)))) (p (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (p
        (0 : Fin (4 : ℕ))) (p (Fin.succ (2 : Fin (3 : ℕ)))) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2
        (p (Fin.succ (2 : Fin (3 : ℕ)))) (p (0 : Fin (4 : ℕ)))) → ((BandVectors.1 (p 0) (p 3) =
        xv) → (xv = I * BandVectors.1 (p 3) (p 0))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I xv pflip hxcoordV
  rw [← hxcoordV]
  simpa using pflip.1

private theorem hza :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xv := BandVectors.1 (r 1) (r 3)
    (-I * I = 1) → ((xv = I * BandVectors.1 (p 3) (p 0)) → (BandVectors.1 (p 3) (p 0) = -I * xv))
        := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I xv hIneg hxv
  calc
    _ = 1 * BandVectors.1 (p 3) (p 0) := by simp
    _ = (-I * I) * BandVectors.1 (p 3) (p 0) := by rw [hIneg]
    _ = -I * (I * BandVectors.1 (p 3) (p 0)) := by
      simp [mul_assoc]
    _ = _ := by rw [← hxv]

private theorem hxa :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xa := BandVectors.2 (r 1) (r 3)
    let e : GaussianInt := -I
    (BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (Fin.succ (2 : Fin (3 : ℕ)))) = ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (p (Fin.succ (2 : Fin (3 : ℕ)))) (p (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (p
        (0 : Fin (4 : ℕ))) (p (Fin.succ (2 : Fin (3 : ℕ)))) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2
        (p (Fin.succ (2 : Fin (3 : ℕ)))) (p (0 : Fin (4 : ℕ)))) → ((BandVectors.2 (p 0) (p 3) =
        xa) → (xa = e * BandVectors.2 (p 3) (p 0))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I xa e pflip hxcoordA
  rw [← hxcoordA]
  simpa [e, I] using pflip.2

private theorem hzaA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xa := BandVectors.2 (r 1) (r 3)
    let e : GaussianInt := -I
    (-e * e = 1) → ((xa = e * BandVectors.2 (p 3) (p 0)) → (BandVectors.2 (p 3) (p 0) = -e * xa))
        := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I xa e heneg hxa
  calc
    _ = 1 * BandVectors.2 (p 3) (p 0) := by simp
    _ = (-e * e) * BandVectors.2 (p 3) (p 0) := by rw [heneg]
    _ = -e * (e * BandVectors.2 (p 3) (p 0)) := by
      simp [mul_assoc]
    _ = _ := by rw [← hxa]

private theorem hminusVecV :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xv := BandVectors.1 (r 1) (r 3)
    (BandVectors.1 (p 0) (p 3) = xv) → ((BandVectors.1 (p 3) (p 0) = -I * xv) → (BandVectors.1 (p
        3) (p 0) - BandVectors.1 (p 0) (p 3) =
      -I * xv - xv)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I xv hxcoordV hza
  rw [hza, hxcoordV]

private theorem hplusVecV :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xv := BandVectors.1 (r 1) (r 3)
    (BandVectors.1 (p 0) (p 3) = xv) → ((BandVectors.1 (p 3) (p 0) = -I * xv) → (BandVectors.1 (p
        3) (p 0) + BandVectors.1 (p 0) (p 3) =
      -I * xv + xv)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I xv hxcoordV hza
  rw [hza, hxcoordV]

private theorem hminusVecA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xa := BandVectors.2 (r 1) (r 3)
    let e : GaussianInt := -I
    (BandVectors.2 (p 0) (p 3) = xa) → ((BandVectors.2 (p 3) (p 0) = -e * xa) → (BandVectors.2 (p
        3) (p 0) - BandVectors.2 (p 0) (p 3) =
      -e * xa - xa)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I xa e hxcoordA hzaA
  rw [hzaA, hxcoordA]

private theorem hplusVecA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xa := BandVectors.2 (r 1) (r 3)
    let e : GaussianInt := -I
    (BandVectors.2 (p 0) (p 3) = xa) → ((BandVectors.2 (p 3) (p 0) = -e * xa) → (BandVectors.2 (p
        3) (p 0) + BandVectors.2 (p 0) (p 3) =
      -e * xa + xa)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I xa e hxcoordA hzaA
  rw [hzaA, hxcoordA]

private theorem houterA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
        ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
        3).2 - (p 1).2), p 0, p 2, p 3]) → (F.q a.succ = p 0) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep
  have h := congrFun hstep 1
  simpa using h

private theorem hindicesA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    F.q ((a + 2).succ) = r 3 ∧ F.q ((a + 1).succ) = r 2 := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r
  constructor <;> rfl

private theorem hvecA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let wa := BandVectors.2 (r 3) (r 2)
    (F.q ((a + 2).succ) = r 3 ∧ F.q ((a + 1).succ) = r 2) → (BandVectors.2 (F.q ((a + 2).succ))
        (F.q ((a + 1).succ)) = wa) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r wa hindicesA
  rw [hindicesA.1, hindicesA.2]

private theorem hindicesJ :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (F.slot + 2 = a + 1) → ((F.slot + 1 = a) → (F.q ((F.slot + 2).succ) = r 2 ∧
      F.q ((F.slot + 1).succ) = r 1)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hslotplus2 hslotplus1
  rw [hslotplus2, hslotplus1]
  constructor <;> rfl

private theorem hvecJ :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let ya := BandVectors.2 (r 2) (r 1)
    (F.q ((F.slot + 2).succ) = r 2 ∧ F.q ((F.slot + 1).succ) = r 1) → (BandVectors.2 (F.q
        ((F.slot + 2).succ))
      (F.q ((F.slot + 1).succ)) = ya) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r ya hindicesJ
  rw [hindicesJ.1, hindicesJ.2]

private theorem hpositiveSlot :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), 0 < (F.q
        F.slot.succ).1 := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F
  rw [F.parent]
  exact C.2

private theorem hrootAEq :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (rootA : ℝ × ℝ),
        (PartialOdometerSlope F.odometer = some rootA) → (rootA = F.outerSlope) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F rootA hrootA
  exact Option.some.inj (hrootA.symm.trans F.slope_outer)

private abbrev hrootJEq := ApollonianSuperharmonic.FrameDiagonalProof.hrootAEq

private theorem slopeK :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let e : GaussianInt := -I
    (BandVectors.2 (F.q ((a + 2).succ)) (F.q ((a + 1).succ)) = wa) → (∀ (sA : ℝ × ℝ), (sA.1 -
        F.outerSlope.1 = (if true = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
        ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 :
        ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 :
        Fin (3 : ℕ))).succ)).im : ℝ))) → ((sA.2 - F.outerSlope.2 = (if true = true then (1 : ℝ)
        else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q
        (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
        ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (sA - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint (wa - e * wa)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa e hvecA sA hARe hAIm
  have hre := hARe
  have him := hAIm
  rw [hvecA] at hre him
  change sA.1 - F.outerSlope.1 = 1 * (1 / 2 : ℝ) *
    (((wa.re : ℤ) : ℝ) - ((wa.im : ℤ) : ℝ)) at hre
  change sA.2 - F.outerSlope.2 = 1 * (1 / 2 : ℝ) *
    (((wa.im : ℤ) : ℝ) + ((wa.re : ℤ) : ℝ)) at him
  apply Prod.ext
  · simp [GaussianRealPoint, e, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre ⊢
    linarith
  · simp [GaussianRealPoint, e, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at him ⊢
    linarith

private theorem slopeJ :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let ya := BandVectors.2 (r 2) (r 1)
    let e : GaussianInt := -I
    (BandVectors.2 (F.q ((F.slot + 2).succ)) (F.q ((F.slot + 1).succ)) = ya) → (∀ (sJ : ℝ × ℝ),
        (sJ.1 - F.outerSlope.1 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
        ((↑(BandVectors.2 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 :
        ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
        (F.slot + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((sJ.2 - F.outerSlope.2 = (if false =
        true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (F.slot + (2 :
        Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2
        (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)).re :
        ℝ))) → (sJ - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint (-(ya - e * ya))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I ya e hvecJ sJ hJRe hJIm
  have hre := hJRe
  have him := hJIm
  rw [hvecJ] at hre him
  change sJ.1 - F.outerSlope.1 = -1 * (1 / 2 : ℝ) *
    (((ya.re : ℤ) : ℝ) - ((ya.im : ℤ) : ℝ)) at hre
  change sJ.2 - F.outerSlope.2 = -1 * (1 / 2 : ℝ) *
    (((ya.im : ℤ) : ℝ) + ((ya.re : ℤ) : ℝ)) at him
  apply Prod.ext
  · simp [GaussianRealPoint, e, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre ⊢
    linarith
  · simp [GaussianRealPoint, e, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at him ⊢
    linarith

private theorem slopeMinusRoot :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (F.q F.slot.succ = r 3) → ((F.q 0 = r 0) → (
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    (BandVectors.2 (r 3) (r 0) = wa + I * xa) → ((BandVectors.2 (r 0) (r 3) = -I * BandVectors.2
        (r 3) (r 0)) → (
    let e : GaussianInt := -I
    F.minusSlope - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint ((wa - e * xa) - e * (wa - e * xa)))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hparentR hzero I wa xa ain aflip' e
  have h := F.minus_difference
  change F.minusSlope - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint
    (BandVectors.2 (F.q F.slot.succ) (F.q 0) -
      BandVectors.2 (F.q 0) (F.q F.slot.succ)) at h
  rw [hparentR, hzero, aflip', ain] at h
  simpa [e, I] using h

private theorem slopeMinusA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (-(wa - -I * wa) - (xa - -I * ya - -I * (xa - -I * ya)) = (2 : GaussianInt) * ya ∧ xa - -I *
        ya + -I * (xa - -I * ya) + (wa - -I * wa) = (2 : GaussianInt) * -I * xa ∧ -(xa - -I * xa)
        - (wa - -I * wa) = ya - -I * ya ∧ ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) =
        ya + -I * ya ∧ wa - -I * xa - -I * (wa - -I * xa) - (wa - -I * wa) = - -I * xa - xa ∧
        -(ya - -I * ya) - (wa - -I * wa) = - -I * xa + xa ∧ ya - -I * wa - -I * (ya - -I * wa) -
        (ya - -I * ya) = - -I * wa - wa ∧ -(xa - -I * xa) - (ya - -I * ya) = - -I * wa + wa ∧
        -(ya - -I * ya) - (xa - -I * xa) = wa - -I * wa ∧ wa - -I * xa + -I * (wa - -I * xa) -
        (xa - -I * xa) = wa + -I * wa) → ((∀ {X : GaussianInt}, ∀ {Y : GaussianInt}, ∀
        {Z : GaussianInt}, (X - Y = Z) → ((1 / 2 : ℝ) • GaussianRealPoint X - (1 / 2 : ℝ) •
        GaussianRealPoint Y = (1 / 2 : ℝ) • GaussianRealPoint Z)) → (
    let e : GaussianInt := -I
    ∀ (sA : ℝ × ℝ), (sA - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint (wa - e * wa)) →
        ((F.minusSlope - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint ((wa - e * xa) - e *
        (wa - e * xa))) → (F.minusSlope - sA =
      (1 / 2 : ℝ) • GaussianRealPoint (-e * xa - xa))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa xa ya ha halfDiff e sA slopeK
      slopeMinusRoot
  calc
    _ = (F.minusSlope - F.outerSlope) - (sA - F.outerSlope) := by abel
    _ = _ := by rw [slopeMinusRoot, slopeK]; exact halfDiff ha.2.2.2.2.1

private theorem slopeJminusA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (-(wa - -I * wa) - (xa - -I * ya - -I * (xa - -I * ya)) = (2 : GaussianInt) * ya ∧ xa - -I *
        ya + -I * (xa - -I * ya) + (wa - -I * wa) = (2 : GaussianInt) * -I * xa ∧ -(xa - -I * xa)
        - (wa - -I * wa) = ya - -I * ya ∧ ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) =
        ya + -I * ya ∧ wa - -I * xa - -I * (wa - -I * xa) - (wa - -I * wa) = - -I * xa - xa ∧
        -(ya - -I * ya) - (wa - -I * wa) = - -I * xa + xa ∧ ya - -I * wa - -I * (ya - -I * wa) -
        (ya - -I * ya) = - -I * wa - wa ∧ -(xa - -I * xa) - (ya - -I * ya) = - -I * wa + wa ∧
        -(ya - -I * ya) - (xa - -I * xa) = wa - -I * wa ∧ wa - -I * xa + -I * (wa - -I * xa) -
        (xa - -I * xa) = wa + -I * wa) → ((∀ {X : GaussianInt}, ∀ {Y : GaussianInt}, ∀
        {Z : GaussianInt}, (X - Y = Z) → ((1 / 2 : ℝ) • GaussianRealPoint X - (1 / 2 : ℝ) •
        GaussianRealPoint Y = (1 / 2 : ℝ) • GaussianRealPoint Z)) → (
    let e : GaussianInt := -I
    ∀ (sA : ℝ × ℝ), ∀ (sJ : ℝ × ℝ), (sA - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint (wa - e
        * wa)) → ((sJ - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint (-(ya - e * ya))) → (sJ -
        sA =
      (1 / 2 : ℝ) • GaussianRealPoint (-e * xa + xa))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa xa ya ha halfDiff e sA sJ slopeK
      slopeJ
  calc
    _ = (sJ - F.outerSlope) - (sA - F.outerSlope) := by abel
    _ = _ := by rw [slopeJ, slopeK]; exact halfDiff ha.2.2.2.2.2.1

private theorem centMinusA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xv := BandVectors.1 (r 1) (r 3)
    (TileCentroid Rminus - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint (-I *
        xv - xv)) → ((BandVectors.1 (p 3) (p 0) - BandVectors.1 (p 0) (p 3) = -I * xv - xv) →
        (TileCentroid Rminus - TileCentroid (D.tiles a true) =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (p 3) (p 0) - BandVectors.1 (p 0) (p 3)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p r I xv hcentR hminusVecV
  rw [hminusVecV]
  exact hcentR

private theorem centJA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), ∀ (J :
        ProtoTile),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let xv := BandVectors.1 (r 1) (r 3)
    (TileCentroid J - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint (-I * xv +
        xv)) → ((BandVectors.1 (p 3) (p 0) + BandVectors.1 (p 0) (p 3) = -I * xv + xv) →
        (TileCentroid J - TileCentroid (D.tiles a true) =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (p 3) (p 0) + BandVectors.1 (p 0) (p 3)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p J r I xv hcentJ hplusVecV
  rw [hplusVecV]
  exact hcentJ

private theorem hodoA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), (F.q
        a.succ = p 0) → (TileOdometer (p 0) (D.tiles a true) (D.functions a true)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p houterA
  simpa [houterA] using D.odometers a true

end FrameDiagonalProof

theorem P4536T1AFrameD
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (a : Fin 3) (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (hstep : ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3])
    (hslot : F.slot = a + 2)
    (hchart : C.1.1.1 = 1 → UnitOccurrenceOrientation p 2 orientation)
    (J : ProtoTile) (hfamily : J ∈ RegularTileFamily base (TilingLattice C))
    (hodo : TileOdometer C.1.1 J (D.functions F.slot false))
    (hcent : TileCentroid J = TileCentroid (D.tiles F.slot false)) :
    ∃ G : P4458T1BoundaryFrame C orientation base Rminus J
        hminus (D.functions F.slot false),
      G.q = p ∧ G.slot = 2 ∧ G.outer.1.1 = F.q a.succ ∧
      G.tile = D.tiles a true ∧ G.odometer = D.functions a true := by
-- BODY
  classical
  let r : Fin 4 → CircleCoordinates :=
    ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
  have hr := FrameDiagonalProof.hrAt128 C orientation base Rminus Rplus
      hminus hplus F a hslot
  have hrstep := FrameDiagonalProof.hrstep C orientation base Rminus Rplus hminus hplus F a p hstep
  have r1 := FrameDiagonalProof.r1 C orientation base Rminus Rplus hminus hplus F a p
      hrstep
  have r2 := FrameDiagonalProof.r2 C orientation base Rminus Rplus hminus hplus F a p
      hrstep
  have r3 := FrameDiagonalProof.r3 C orientation base Rminus Rplus hminus hplus F a p
      hrstep
  have hparent := FrameDiagonalProof.hparent C orientation base Rminus
      Rplus hminus hplus F a p hstep hslot
  have hparentR := FrameDiagonalProof.hparentR C orientation base Rminus
      Rplus hminus hplus F a p r3 hparent
  have hzero := FrameDiagonalProof.hzero C orientation base Rminus Rplus hminus
      hplus F a
  have hC := FrameDiagonalProof.hC C orientation base Rminus Rplus hminus hplus F p
      hparent
  have positiveA := FrameDiagonalProof.positiveA p hp
  let I : GaussianInt := ⟨0, 1⟩
  let xa := BandVectors.2 (r 1) (r 3)
  have laws := FrameDiagonalProof.laws C orientation base Rminus Rplus hminus hplus F a hr
  have hrr := FrameDiagonalProof.hrr C orientation base Rminus Rplus
      hminus hplus F a hr
  have lawsR := FrameDiagonalProof.lawsR C orientation base Rminus Rplus hminus hplus F a hrr
  have win := FrameDiagonalProof.win C orientation base
      Rminus Rplus hminus hplus F a lawsR
  have ain := FrameDiagonalProof.ain C orientation base
      Rminus Rplus hminus hplus F a lawsR
  have hv := FrameDiagonalProof.hv C orientation base Rminus Rplus hminus hplus F a laws
  have ha := FrameDiagonalProof.ha C orientation base Rminus Rplus hminus hplus F a laws
  have vflip := FrameDiagonalProof.vflip C orientation base Rminus Rplus hminus hplus F a hr laws
  have vflip' := FrameDiagonalProof.vflip' C orientation base Rminus Rplus hminus hplus F a vflip
  have aflip' := FrameDiagonalProof.aflip' C orientation base Rminus Rplus hminus hplus F a vflip
  have centMinus := FrameDiagonalProof.centMinus C orientation base Rminus Rplus hminus hplus F a
      p r3
          hparent hzero win vflip'
  have centJ := FrameDiagonalProof.centJ C orientation
          base Rminus Rplus hminus hplus F D a hslot J hcent
  have centK := FrameDiagonalProof.centK C orientation
          base Rminus Rplus hminus hplus F D a
  have halfDiff {X Y Z : GaussianInt} (hxy : X - Y = Z) := FrameDiagonalProof.halfDiff (X := X)
      (Y := Y) (Z
              := Z) hxy
  have hcentR := FrameDiagonalProof.hcentR C orientation
          base Rminus Rplus hminus hplus F D a hv centMinus centK halfDiff
  have hcentJ := FrameDiagonalProof.hcentJ C orientation
          base Rminus Rplus hminus hplus F D a J hv centJ centK halfDiff
  let e : GaussianInt := -I
  have lawsP := FrameDiagonalProof.lawsP p hp
  have pflip := FrameDiagonalProof.pflip p hp lawsP
  have hxcoordV := FrameDiagonalProof.hxcoordV C orientation
      base Rminus Rplus hminus hplus F a p r1 r3
  have hxcoordA := FrameDiagonalProof.hxcoordA C orientation
      base Rminus Rplus hminus hplus F a p r1 r3
  have hI2 := FrameDiagonalProof.hI2
  have he2 := FrameDiagonalProof.he2
  have hIneg := FrameDiagonalProof.hIneg hI2
  have heneg := FrameDiagonalProof.heneg he2
  have hxv := FrameDiagonalProof.hxv C orientation base
      Rminus Rplus hminus hplus F a p pflip hxcoordV
  have hza := FrameDiagonalProof.hza C orientation base
      Rminus Rplus hminus hplus F a p hIneg hxv
  have hxa := FrameDiagonalProof.hxa C orientation base
      Rminus Rplus hminus hplus F a p pflip hxcoordA
  have hzaA := FrameDiagonalProof.hzaA C orientation base
      Rminus Rplus hminus hplus F a p heneg hxa
  have hminusVecV := FrameDiagonalProof.hminusVecV C orientation base Rminus Rplus hminus hplus
          F a p hxcoordV hza
  have hplusVecV := FrameDiagonalProof.hplusVecV C orientation base Rminus Rplus hminus hplus F
          a p hxcoordV hza
  have hminusVecA : BandVectors.2 (p 3) (p 0) - BandVectors.2 (p 0) (p 3) =
      -e * xa - xa := FrameDiagonalProof.hminusVecA C orientation base Rminus Rplus hminus hplus
          F a p hxcoordA hzaA
  have hplusVecA : BandVectors.2 (p 3) (p 0) + BandVectors.2 (p 0) (p 3) =
      -e * xa + xa := FrameDiagonalProof.hplusVecA C orientation base Rminus Rplus hminus hplus F
          a p hxcoordA hzaA
  have houterA := FrameDiagonalProof.houterA C orientation base Rminus Rplus
      hminus hplus F a p hstep
  let A : BandCircle :=
    ⟨⟨p 0, Or.inl positiveA, p, hp.1, 0, rfl⟩, positiveA⟩
  have hindicesA := FrameDiagonalProof.hindicesA C orientation base Rminus Rplus hminus hplus F a
  have hvecA := FrameDiagonalProof.hvecA C orientation base Rminus Rplus hminus hplus F a hindicesA
  have hslotplus2 : F.slot + 2 = a + 1 := by
    rw [hslot]
    fin_cases a <;> decide
  have hslotplus1 : F.slot + 1 = a := by
    rw [hslot]
    fin_cases a <;> decide
  have hindicesJ := FrameDiagonalProof.hindicesJ C orientation base Rminus
          Rplus hminus hplus F a hslotplus2 hslotplus1
  have hvecJ := FrameDiagonalProof.hvecJ C orientation base Rminus Rplus
          hminus hplus F a hindicesJ
  have hpositiveSlot := FrameDiagonalProof.hpositiveSlot C orientation
      base Rminus Rplus hminus hplus F
  obtain hzA | ⟨rootA, sA, hrootA, hsA, hARe, hAIm⟩ := D.slopes a true
  · rw [houterA] at hzA
    omega
  have hrootAEq := FrameDiagonalProof.hrootAEq C orientation base Rminus
      Rplus hminus hplus F rootA hrootA
  subst rootA
  obtain hzJ | ⟨rootJ, sJ, hrootJ, hsJ, hJRe, hJIm⟩ := D.slopes F.slot false
  · omega
  have hrootJEq := FrameDiagonalProof.hrootJEq C orientation base Rminus
      Rplus hminus hplus F rootJ hrootJ
  subst rootJ
  have slopeK := FrameDiagonalProof.slopeK C orientation
          base Rminus Rplus hminus hplus F a hvecA sA hARe hAIm
  have slopeJ := FrameDiagonalProof.slopeJ C orientation
          base Rminus Rplus hminus hplus F a hvecJ sJ hJRe hJIm
  have slopeMinusRoot := FrameDiagonalProof.slopeMinusRoot C orientation base Rminus Rplus hminus
      hplus F a
          hparentR hzero ain aflip'
  have slopeMinusA := FrameDiagonalProof.slopeMinusA C
          orientation base Rminus Rplus hminus hplus F a ha halfDiff sA slopeK slopeMinusRoot
  have slopeJminusA := FrameDiagonalProof.slopeJminusA C
          orientation base Rminus Rplus hminus hplus F a ha halfDiff sA sJ slopeK slopeJ
  have centMinusA := FrameDiagonalProof.centMinusA
            C orientation base Rminus Rplus hminus hplus F D a p hcentR hminusVecV
  have centJA := FrameDiagonalProof.centJA C
            orientation base Rminus Rplus hminus hplus F D a p J hcentJ hplusVecV
  have hodoA := FrameDiagonalProof.hodoA C orientation base Rminus Rplus hminus hplus F D a p
      houterA
  let G : P4458T1BoundaryFrame C orientation base Rminus J hminus
      (D.functions F.slot false) := {
    outer := A
    q := p
    proper := hp
    slot := 2
    child := rfl
    parent := hC.symm
    tile := D.tiles a true
    odometer := D.functions a true
    outer_odo := by
      simpa [A] using hodoA
    minus_odo := F.minus_odo
    plus_odo := hodo
    outer_band := by
      simpa [A] using TileOdometerBandPrototile _ _ _ hodoA
    base_band := F.base_band
    minus_family := F.minus_family
    plus_family := hfamily
    chart := hchart
    minus_centroid := centMinusA
    plus_centroid := centJA
    outerSlope := sA
    minusSlope := F.minusSlope
    plusSlope := sJ
    slope_outer := hsA
    slope_minus := F.slope_minus
    slope_plus := hsJ
    minus_difference := by
      have h : BandVectors.2 (p (2 : Fin 3).succ) (p 0) -
          BandVectors.2 (p 0) (p (2 : Fin 3).succ) = -e * xa - xa := by
        simpa [e, xa] using hminusVecA
      rw [h]
      exact slopeMinusA
    plus_difference := by
      have h : BandVectors.2 (p (2 : Fin 3).succ) (p 0) +
          BandVectors.2 (p 0) (p (2 : Fin 3).succ) = -e * xa + xa := by
        simpa [e, xa] using hplusVecA
      rw [h]
      exact slopeJminusA
  }
  refine ⟨G, rfl, rfl, ?_, rfl, rfl⟩
  exact houterA.symm

end ApollonianSuperharmonic

end
