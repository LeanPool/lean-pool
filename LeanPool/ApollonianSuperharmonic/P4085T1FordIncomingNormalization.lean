/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordRegimeConverse
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProjectiveVectorCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.P4085T1RestrictedAdaptedActions

-- [TABLET NODE: P4085T1FordIncomingNormalization]

/-!
# P4085T1FordIncomingNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4085T1FordIncomingNormalization
    (r : Fin 4 → CircleCoordinates) (hproper : ProperBandQuadruple r)
    (hline : ∃ j : Fin 4, (r j).1 = 0)
    (i : Fin 3) (s : Fin 4) (U W : ProtoTile)
    (hU : BandPrototile (r 0) U) (hW : BandPrototile (r i.succ) W)
    (hUpos : 0 < (r 0).1) (hWpos : 0 < (r i.succ).1)
    (hcent : TileCentroid W - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ)))) :
    ∃ (a : Fin 3) (g : BandPackingSymmetry) (P : FordFareyParameter),
      1 < P.q ∧
      let k : Fin 3 := i - a
      let q := FordRecursiveQuadruple P
      BandPackingSymmetryQuadrupleAction g
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ] = q ∧
      q k.succ = BandPackingSymmetryCircleAction g (r i.succ) ∧
      BandPrototile (q 0) (BandPackingSymmetryTileAction g U) ∧
      BandPrototile (q k.succ) (BandPackingSymmetryTileAction g W) ∧
      0 < (q 0).1 ∧ 0 < (q k.succ).1 ∧
      TileCentroid (BandPackingSymmetryTileAction g W) -
          TileCentroid (BandPackingSymmetryTileAction g U) =
        (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (q k.succ) (q 0) + BandVectors.1 (q 0) (q k.succ))) ∧
      BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (r i.succ) (r 0)
            else BandVectors.1 (r 0) (r i.succ))) =
        (⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q k.succ) (q 0)
            else BandVectors.1 (q 0) (q k.succ)) := by
-- BODY
  obtain ⟨a, g₀, P, hP, hg₀, hw, _, heq⟩ := FordRegimeConverse r hproper hline
  let p : Fin 4 → CircleCoordinates :=
    ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
  have hp : ProperBandQuadruple p := by
    fin_cases a
    · convert hproper using 1; funext x; fin_cases x <;> rfl
    · refine ⟨SemiProperQuadruple.rotate hproper.1, ?_⟩
      intro j
      fin_cases j
      · simpa [p] using hproper.2 (1 : Fin 3)
      · simpa [p] using hproper.2 (2 : Fin 3)
      · simpa [p] using hproper.2 (0 : Fin 3)
    · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hproper.1), ?_⟩
      intro j
      fin_cases j
      · simpa [p] using hproper.2 (2 : Fin 3)
      · simpa [p] using hproper.2 (0 : Fin 3)
      · simpa [p] using hproper.2 (1 : Fin 3)
  have projective := BandPackingSymmetryProjectiveVectorCovariance g₀ p hp
  dsimp only at projective
  rcases projective with ⟨_, _, _, _, _, _, _, _, g, hlift, _, hpar, hquad, hphase, _, _⟩
  have hg : BandPackingSymmetryReversesOrientation g = false := hpar.trans hg₀
  obtain ⟨m, _, hvector, hcentroid⟩ :=
    P4085T1RestrictedAdaptedActions g₀ g hw hlift
  have hadd (x y : GaussianInt) :
      BandPackingSymmetryVectorAction g (x + y) =
        BandPackingSymmetryVectorAction g x + BandPackingSymmetryVectorAction g y := by
    simp only [hvector, mul_add]
  have hcomm (x : GaussianInt) :
      BandPackingSymmetryVectorAction g ((⟨0, 1⟩ : GaussianInt) ^ s.val * x) =
        (⟨0, 1⟩ : GaussianInt) ^ s.val * BandPackingSymmetryVectorAction g x := by
    simp only [hvector]
    ring
  let k : Fin 3 := i - a
  let q := FordRecursiveQuadruple P
  have hnormal : BandPackingSymmetryQuadrupleAction g p = q := (hquad p).trans heq
  have hroot : q 0 = BandPackingSymmetryCircleAction g (r 0) := by
    rw [← hnormal]
    rfl
  have hparent : q k.succ = BandPackingSymmetryCircleAction g (r i.succ) := by
    rw [← hnormal]
    fin_cases a <;> fin_cases i <;>
      simp [k, p, BandPackingSymmetryQuadrupleAction, hg]
  have hpk : p k.succ = r i.succ := by
    fin_cases a <;> fin_cases i <;> rfl
  have hforward : BandVectors.1 (q k.succ) (q 0) =
      BandPackingSymmetryVectorAction g (BandVectors.1 (r i.succ) (r 0)) := by
    have h := (hphase k).1
    simpa only [BandPackingSymmetryScopedPhase, hg, Bool.false_eq_true,
      ite_false, one_mul, hnormal, hpk, p, Matrix.cons_val_zero] using h
  have hbackward : BandVectors.1 (q 0) (q k.succ) =
      BandPackingSymmetryVectorAction g (BandVectors.1 (r 0) (r i.succ)) := by
    have h := (hphase k).2.1
    simpa only [BandPackingSymmetryScopedPhase, hg, Bool.false_eq_true,
      ite_false, one_mul, hnormal, hpk, p, Matrix.cons_val_zero] using h
  have hc := hcentroid U W _ hcent
  rw [hcomm, hadd, ← hforward, ← hbackward] at hc
  have hdisp : BandPackingSymmetryVectorAction g
      ((⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (r i.succ) (r 0)
          else BandVectors.1 (r 0) (r i.succ))) =
      (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q k.succ) (q 0)
          else BandVectors.1 (q 0) (q k.succ)) := by
    rw [hcomm]
    split_ifs <;> simp only [← hforward, ← hbackward]
  have cov := BandPackingSymmetryCovariance g
  refine ⟨a, g, P, hP, hnormal, hparent, ?_, ?_, ?_, ?_, hc, hdisp⟩
  · change BandPrototile (q 0) _
    rw [hroot]
    exact (cov.2.1 _ _).mp hU
  · change BandPrototile (q k.succ) _
    rw [hparent]
    exact (cov.2.1 _ _).mp hW
  · change 0 < (q 0).1
    rw [hroot, cov.1]
    exact hUpos
  · change 0 < (q k.succ).1
    rw [hparent, cov.1]
    exact hWpos

end ApollonianSuperharmonic

end
